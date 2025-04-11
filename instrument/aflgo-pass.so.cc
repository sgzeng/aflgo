/*
   aflgo - LLVM instrumentation pass
   ---------------------------------

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

 */

#define AFL_LLVM_PASS

#include "../afl-2.57b/config.h"
#include "../afl-2.57b/debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <list>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/CFGPrinter.h"
#include "llvm/Support/DJB.h"

#if defined(LLVM34)
#include "llvm/DebugInfo.h"
#else
#include "llvm/IR/DebugInfo.h"
#endif

#if defined(LLVM34) || defined(LLVM35) || defined(LLVM36)
#define LLVM_OLD_DEBUG_API
#endif

using namespace llvm;

cl::opt<std::string> DistanceFile(
    "distance",
    cl::desc("Distance file containing the distance of each basic block to the provided targets."),
    cl::value_desc("filename")
);

cl::opt<std::string> TargetsFile(
    "targets",
    cl::desc("Input file containing the target lines of code."),
    cl::value_desc("targets"));

cl::opt<std::string> OutDirectory(
    "outdir",
    cl::desc("Output directory where Ftargets.txt, Fnames.txt, and BBnames.txt are generated."),
    cl::value_desc("outdir"));

namespace llvm {

/// \brief Retrieve the first available debug location in \p BB that is not
/// inside /usr/ and store the **absolute, normalized path** in \p Filename.
/// Sets \p Line and \p Col accordingly.
///
/// This version does:
///  1) Loops over instructions in \p BB
///  2) Checks the debug location (and possibly inlined-at location)
///  3) Builds an absolute, normalized path (resolving "." and "..")
///  4) Skips if the path is empty, line=0, or the path starts with "/usr/"
///  5) Returns the first valid debug info found
void getDebugLocationFullPath(const BasicBlock *BB,
                              std::string &Filename,
                              unsigned &Line,
                              unsigned &Col) {
  Filename.clear();
  Line = 0;
  Col = 0;

  // We don't want paths that point to system libraries in /usr/
  static const std::string Xlibs("/usr/");

  // Iterate over instructions in the basic block
  for (auto &Inst : *BB) {
    if (DILocation *Loc = Inst.getDebugLoc()) {
      // Extract directory & filename
      std::string Dir  = Loc->getDirectory().str();
      std::string File = Loc->getFilename().str();
      unsigned    L    = Loc->getLine();
      unsigned    C    = Loc->getColumn();

      // If there's no filename, check the inlined location
      if (File.empty()) {
        if (DILocation *inlinedAt = Loc->getInlinedAt()) {
          Dir  = inlinedAt->getDirectory().str();
          File = inlinedAt->getFilename().str();
          L    = inlinedAt->getLine();
          C    = inlinedAt->getColumn();
        }
      }

      // Skip if still no filename or line==0
      if (File.empty() || L == 0)
        continue;

      // Build an absolute path in a SmallString
      llvm::SmallString<256> FullPath;

      // 1) If Dir is already absolute, just start with that.
      //    Otherwise, use the current working directory as a base.
      if (!Dir.empty() && llvm::sys::path::is_absolute(Dir)) {
        FullPath = Dir;
      } else {
        llvm::sys::fs::current_path(FullPath); // get the current working dir
        if (!Dir.empty()) {
          llvm::sys::path::append(FullPath, Dir);
        }
      }

      // 2) Append the filename
      llvm::sys::path::append(FullPath, File);

      // 3) Remove dot segments (both "." and "..")
      llvm::sys::path::remove_dots(FullPath, /*remove_dot_dot=*/true);

      // Now FullPath is absolute & normalized
      // Check if it's in /usr/
      if (StringRef(FullPath).startswith(Xlibs))
        continue; // skip system-libs

      // Found a valid location => set output vars
      Filename = FullPath.str().str(); // convert to std::string
      Line     = L;
      Col      = C;
      break; // stop after the first valid location
    }
  }
}

void getInsDebugLoc(const Instruction *I, std::string &Filename,
                        unsigned &Line, unsigned &Col) {
  std::string filename;
  if (DILocation *Loc = I->getDebugLoc()) {
    Line = Loc->getLine();
    filename = Loc->getFilename().str();
    Col = Loc->getColumn();
    if (filename.empty()) {
      DILocation *oDILoc = Loc->getInlinedAt();
      if (oDILoc) {
        Line = oDILoc->getLine();
        Col = oDILoc->getColumn();
        filename = oDILoc->getFilename().str();
      }
    }
    std::size_t found = filename.find_last_of("/\\");
    if (found != std::string::npos)
      filename = filename.substr(found + 1);
    Filename = filename;
  }
}

void getBBDebugLoc(const BasicBlock *BB, std::string &Filename, unsigned &Line, unsigned &Col) {
  std::string bb_name("");
  std::string filename;
  unsigned line = 0;
  unsigned col = 0;
  for (auto &I : *BB) {
    getInsDebugLoc(&I, filename, line, col);
    /* Don't worry about external libs */
    static const std::string Xlibs("/usr/");
    if (filename.empty() || line == 0 || !filename.compare(0, Xlibs.size(), Xlibs))
      continue;
    Filename = filename;
    Line = line;
    Col = col;
    break;
  }
}

void getFuncDebugLoc(const Function *F, std::string &Filename, unsigned &Line) {
  if (F == nullptr || F->empty()) return;
    // Again assuming the debug location is attached to the first instruction of the function.
    const BasicBlock &entry = F->getEntryBlock();
    if (entry.empty()) return;
    const Instruction *I = entry.getFirstNonPHIOrDbg();
    if (I == nullptr) return;
    unsigned col = 0;
    getInsDebugLoc(I, Filename, Line, col);
}

uint32_t getBasicblockId(BasicBlock &BB, std::string &filename, unsigned &line, unsigned &col) {
  static uint32_t unamed = 0;
  std::string bb_name_with_col("");
  getBBDebugLoc(&BB, filename, line, col);
  if (!filename.empty() && line != 0 ){
    bb_name_with_col = filename + ":" + std::to_string(line) + ":" + std::to_string(col);
  }else{
    bb_name_with_col = filename + ":unamed:" + std::to_string(unamed++);
  }
  return djbHash(bb_name_with_col);
}

template<>
struct DOTGraphTraits<Function*> : public DefaultDOTGraphTraits {
  DOTGraphTraits(bool isSimple=true) : DefaultDOTGraphTraits(isSimple) {}

  static std::string getGraphName(Function *F) {
    return "CFG for '" + F->getName().str() + "' function";
  }

  std::string getNodeLabel(BasicBlock *Node, Function *Graph) {
    if (!Node->getName().empty()) {
      return Node->getName().str();
    }

    std::string Str;
    raw_string_ostream OS(Str);

    Node->printAsOperand(OS, false);
    return OS.str();
  }
};

} // namespace llvm

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}

char AFLCoverage::ID = 0;

static void getDebugLoc(const Instruction *I, std::string &Filename,
                        unsigned &Line) {
#ifdef LLVM_OLD_DEBUG_API
  DebugLoc Loc = I->getDebugLoc();
  if (!Loc.isUnknown()) {
    DILocation cDILoc(Loc.getAsMDNode(M.getContext()));
    DILocation oDILoc = cDILoc.getOrigLocation();

    Line = oDILoc.getLineNumber();
    Filename = oDILoc.getFilename().str();

    if (filename.empty()) {
      Line = cDILoc.getLineNumber();
      Filename = cDILoc.getFilename().str();
    }
  }
#else
  if (DILocation *Loc = I->getDebugLoc()) {
    Line = Loc->getLine();
    Filename = Loc->getFilename().str();

    if (Filename.empty()) {
      DILocation *oDILoc = Loc->getInlinedAt();
      if (oDILoc) {
        Line = oDILoc->getLine();
        Filename = oDILoc->getFilename().str();
      }
    }
  }
#endif /* LLVM_OLD_DEBUG_API */
}

static bool isBlacklisted(const Function *F) {
  static const SmallVector<std::string, 8> Blacklist = {
    "asan.",
    "llvm.",
    "sancov.",
    "__ubsan_handle_",
    "free",
    "malloc",
    "calloc",
    "realloc"
  };

  for (auto const &BlacklistFunc : Blacklist) {
    if (F->getName().startswith(BlacklistFunc)) {
      return true;
    }
  }

  return false;
}

bool AFLCoverage::runOnModule(Module &M) {

  bool is_aflgo = false;
  bool is_aflgo_preprocessing = false;

  if (!TargetsFile.empty() && !DistanceFile.empty()) {
    FATAL("Cannot specify both '-targets' and '-distance'!");
    return false;
  }

  std::list<std::string> targets;
  std::map<uint64_t, int> bb_to_dis;
  std::vector<std::string> basic_blocks;

  if (!TargetsFile.empty()) {

    if (OutDirectory.empty()) {
      FATAL("Provide output directory '-outdir <directory>'");
      return false;
    }

    std::ifstream targetsfile(TargetsFile);
    std::string line;
    while (std::getline(targetsfile, line))
      targets.push_back(line);
    targetsfile.close();

    is_aflgo_preprocessing = true;

  } else if (!DistanceFile.empty()) {

    std::ifstream cf(DistanceFile);
    if (cf.is_open()) {
      std::string line;
      while (getline(cf, line)) {
        if (line.empty()) continue;
        std::stringstream ss(line);
        std::string token;
        uint64_t BB_id;
        int bb_dis;
        // Read BB_id
        if (!getline(ss, token, ',')) continue;
        std::stringstream bb_id_ss(token);
        if (!(bb_id_ss >> BB_id)) continue;
        // Skip filename:loc
        if (!getline(ss, token, ',')) continue;
        // Read distance
        if (!getline(ss, token, ',')) continue;
        std::stringstream dis_ss(token);
        if (!(dis_ss >> bb_dis)) continue;
        bb_to_dis.emplace(BB_id, bb_dis);
      }
      cf.close();

      is_aflgo = true;

    } else {
      FATAL("Unable to find %s.", DistanceFile.c_str());
      return false;
    }

  }

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    if (is_aflgo || is_aflgo_preprocessing)
      SAYF(cCYA "aflgo-llvm-pass (yeah!) " cBRI VERSION cRST " (%s mode)\n",
           (is_aflgo_preprocessing ? "preprocessing" : "distance instrumentation"));
    else
      SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");


  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Default: Not selective */
  char* is_selective_str = getenv("AFLGO_SELECTIVE");
  unsigned int is_selective = 0;

  if (is_selective_str && sscanf(is_selective_str, "%u", &is_selective) != 1)
    FATAL("Bad value of AFLGO_SELECTIVE (must be 0 or 1)");

  char* dinst_ratio_str = getenv("AFLGO_INST_RATIO");
  unsigned int dinst_ratio = 100;

  if (dinst_ratio_str) {

    if (sscanf(dinst_ratio_str, "%u", &dinst_ratio) != 1 || !dinst_ratio ||
        dinst_ratio > 100)
      FATAL("Bad value of AFLGO_INST_RATIO (must be between 1 and 100)");

  }

  /* Instrument all the things! */

  int inst_blocks = 0;

  if (is_aflgo_preprocessing) {

    std::ofstream bbnames(OutDirectory + "/BBnames.txt", std::ofstream::out | std::ofstream::app);
    std::ofstream bbcalls(OutDirectory + "/BBcalls.txt", std::ofstream::out | std::ofstream::app);
    std::ofstream fnames(OutDirectory + "/Fnames.txt", std::ofstream::out | std::ofstream::app);
    std::ofstream ftargets(OutDirectory + "/Ftargets.txt", std::ofstream::out | std::ofstream::app);

    /* Create dot-files directory */
    std::string dotfiles(OutDirectory + "/dot-files");
    if (sys::fs::create_directory(dotfiles)) {
      FATAL("Could not create directory %s.", dotfiles.c_str());
    }

    for (auto &F : M) {

      bool has_BBs = false;
      std::string funcName = F.getName().str();

      /* Black list of function names */
      if (isBlacklisted(&F)) {
        continue;
      }

      bool is_target = false;
      for (auto &BB : F) {

        std::string bb_name("");
        std::string filename;
        unsigned line;

        for (auto &I : BB) {
          getDebugLoc(&I, filename, line);

          /* Don't worry about external libs */
          static const std::string Xlibs("/usr/");
          if (filename.empty() || line == 0 || !filename.compare(0, Xlibs.size(), Xlibs))
            continue;

          std::size_t found = filename.find_last_of("/\\");
          if (found != std::string::npos)
            filename = filename.substr(found + 1);

          if (bb_name.empty()) 
            bb_name = filename + ":" + std::to_string(line);
          
          if (!is_target) {
            for (auto &target : targets) {
              std::size_t found = target.find_last_of("/\\");
              if (found != std::string::npos)
                target = target.substr(found + 1);

              std::size_t pos = target.find_last_of(":");
              std::string target_file = target.substr(0, pos);
              unsigned int target_line = atoi(target.substr(pos + 1).c_str());

              if (!target_file.compare(filename) && target_line == line)
                is_target = true;

            }
          }

          if (auto *c = dyn_cast<CallInst>(&I)) {

            std::size_t found = filename.find_last_of("/\\");
            if (found != std::string::npos)
              filename = filename.substr(found + 1);

            if (auto *CalledF = c->getCalledFunction()) {
              if (!isBlacklisted(CalledF))
                bbcalls << bb_name << "," << CalledF->getName().str() << "\n";
            }
          }
        }

        if (!bb_name.empty()) {

          BB.setName(bb_name + ":");
          if (!BB.hasName()) {
            std::string newname = bb_name + ":";
            Twine t(newname);
            SmallString<256> NameData;
            StringRef NameRef = t.toStringRef(NameData);
            MallocAllocator Allocator;
            BB.setValueName(ValueName::Create(NameRef, Allocator));
          }

          bbnames << BB.getName().str() << "\n";
          has_BBs = true;

#ifdef AFLGO_TRACING
          auto *TI = BB.getTerminator();
          IRBuilder<> Builder(TI);

          Value *bbnameVal = Builder.CreateGlobalStringPtr(bb_name);
          Type *Args[] = {
              Type::getInt8PtrTy(M.getContext()) //uint8_t* bb_name
          };
          FunctionType *FTy = FunctionType::get(Type::getVoidTy(M.getContext()), Args, false);
          Constant *instrumented = M.getOrInsertFunction("llvm_profiling_call", FTy);
          Builder.CreateCall(instrumented, {bbnameVal});
#endif

        }
      }

      if (has_BBs) {
        /* Print CFG */
        std::string cfgFileName = dotfiles + "/cfg." + funcName + ".dot";
        std::error_code EC;
        raw_fd_ostream cfgFile(cfgFileName, EC, sys::fs::F_None);
        if (!EC) {
          WriteGraph(cfgFile, &F, true);
        }

        if (is_target)
          ftargets << F.getName().str() << "\n";
        fnames << F.getName().str() << "\n";
      }
    }

  } else {
    /* Distance instrumentation */

    LLVMContext &C = M.getContext();
    IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
    IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
    IntegerType *Int64Ty = IntegerType::getInt64Ty(C);

#ifdef __x86_64__
    IntegerType *LargestType = Int64Ty;
    ConstantInt *MapCntLoc = ConstantInt::get(LargestType, MAP_SIZE + 8);
#else
    IntegerType *LargestType = Int32Ty;
    ConstantInt *MapCntLoc = ConstantInt::get(LargestType, MAP_SIZE + 4);
#endif
    ConstantInt *MapDistLoc = ConstantInt::get(LargestType, MAP_SIZE);
    ConstantInt *One = ConstantInt::get(LargestType, 1);

    /* Get globals for the SHM region and the previous location. Note that
       __afl_prev_loc is thread-local. */

    GlobalVariable *AFLMapPtr =
        new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                           GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

    GlobalVariable *AFLPrevLoc = new GlobalVariable(
        M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
        0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

    for (auto &F : M) {

      int distance = -1;

      for (auto &BB : F) {

        distance = -2;

        if (is_aflgo) {
          /* Find distance for BB */
          std::string filename;
          unsigned line = 0;
          unsigned col = 0;
          uint64_t bb_id = (uint64_t) getBasicblockId(BB, filename, line, col);
          if (bb_to_dis.find(bb_id) != bb_to_dis.end()) {
            /* Find distance for BB */
            distance = bb_to_dis[bb_id];
            SAYF("found distance(%d) for BB_ID(%lu)\n", distance, bb_id);
          }
        }

        BasicBlock::iterator IP = BB.getFirstInsertionPt();
        IRBuilder<> IRB(&(*IP));

        if (AFL_R(100) >= inst_ratio) continue;

        /* Make up cur_loc */

        unsigned int cur_loc = AFL_R(MAP_SIZE);

        ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

        /* Load prev_loc */

        LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
        PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

        /* Load SHM pointer */

        LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
        MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *MapPtrIdx =
            IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

        /* Update bitmap */

        LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
        Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
        IRB.CreateStore(Incr, MapPtrIdx)
           ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        /* Set prev_loc to cur_loc >> 1 */

        StoreInst *Store =
            IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
        Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

        if (distance >= 0) {
          ConstantInt *Distance = ConstantInt::get(LargestType, (uint64_t) distance);

          /* Store global minimal BB distance to shm[MAPSIZE]
          *  sub = distance - map_dist
          *  lshr = sign(sub) 
          *  shm[MAPSIZE] = lshr * distance + (1 - lshr) * map_dist
          */
          Value *MapDistPtr = IRB.CreateBitCast(
              IRB.CreateGEP(MapPtr, MapDistLoc), LargestType->getPointerTo());
          LoadInst *MapDist = IRB.CreateLoad(MapDistPtr);
          MapDist->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          Value *Sub = IRB.CreateSub(Distance, MapDist);
          ConstantInt *Bits = ConstantInt::get(LargestType, 63);
          Value *Lshr = IRB.CreateLShr(Sub, Bits);
          Value *Mul1 = IRB.CreateMul(Lshr, Distance);
          Value *Sub1 = IRB.CreateSub(One, Lshr);
          Value *Mul2 = IRB.CreateMul(Sub1, MapDist);
          Value *Incr = IRB.CreateAdd(Mul1, Mul2);

          IRB.CreateStore(Incr, MapDistPtr)
           ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          /* Increase count at shm[MAPSIZE + (4 or 8)] */
          Value *MapCntPtr = IRB.CreateBitCast(
              IRB.CreateGEP(MapPtr, MapCntLoc), LargestType->getPointerTo());
          LoadInst *MapCnt = IRB.CreateLoad(MapCntPtr);
          MapCnt->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

          Value *IncrCnt = IRB.CreateAdd(MapCnt, One);
          IRB.CreateStore(IncrCnt, MapCntPtr)
              ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));


        }else if (distance == -1){
          llvm::FunctionCallee exitFunc = M.getOrInsertFunction(
              "exit", llvm::FunctionType::get(
                llvm::Type::getVoidTy(M.getContext()), Int32Ty, false));
          IRB.CreateCall(exitFunc, {IRB.getInt32(0)});
        }

        inst_blocks++;

      }
    }
  }

  /* Say something nice. */

  if (!is_aflgo_preprocessing && !be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%, dist. ratio %u%%).",
             inst_blocks,
             getenv("AFL_HARDEN")
             ? "hardened"
             : ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN"))
               ? "ASAN/MSAN" : "non-hardened"),
             inst_ratio, dinst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
