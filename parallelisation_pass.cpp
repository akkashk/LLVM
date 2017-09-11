#include "llvm/Pass.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/InstIterator.h"

#include "llvm/Support/raw_ostream.h"

#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/DependenceAnalysis.h"

#include <stdlib.h>
#include <algorithm>
#include <queue>
#include <vector>

#define OUTPUTT false
#define DEBUGG false
#define DEBUGPHI false
#define DEPENDENCY false
#define MAPPING false

using namespace llvm;

namespace{
	struct parallelise : public FunctionPass{
		static char ID;
		unsigned int core_count = 2;							// Change this value to control how many threads are spawned
		int counter = 0;
		std::map<Value*, std::vector<Instruction*>> mapping;	// Contains a Map os entried {AllocaInst : List of instructions in Loop using that memory}
		StructType* unionattr;
		
		llvm::AtomicOrdering order = llvm::AtomicOrdering::SequentiallyConsistent;
		llvm::SynchronizationScope syncScope = llvm::SynchronizationScope::CrossThread;
		
		std::vector<Instruction*> toPutBetween; // The vector stores every two instructions where to put wait and signal before
		
		parallelise() : FunctionPass(ID) {}
		
		void getAnalysisUsage(AnalysisUsage &AU) const {
			AU.addRequired<LoopInfoWrapperPass>();
			AU.addRequired<DependenceAnalysisWrapperPass>();
			AU.addRequired<DominatorTreeWrapperPass>();
			AU.addRequired<ScalarEvolutionWrapperPass>();
		}
		
		bool doInitialization(Module& M) {
			this->unionattr = this->insertPthreadFunctions(M);
			return true;
		}
		
		bool doFinalization(Module& M) {
			if (OUTPUTT) {errs();}
			errs() << "Number of parallelised loops: " << this->counter << "\n";
			return true;
		}
		
		
		bool hasNoDependencies(Loop* loop) {
			bool noDependency = true;
			std::vector<Loop*> subLoops = loop->getSubLoops();
			DependenceInfo& DI = getAnalysis<DependenceAnalysisWrapperPass>().getDI();
			std::vector<Instruction*> outerLoopIns;
			
			for (Loop::block_iterator it = loop->block_begin(); it!=loop->block_end(); it++) {
				BasicBlock* body = *it;
				
				bool skip = false;
				for (Loop* l : subLoops) {
					if (l->contains(body)) {
						skip = true;
						break;
					}
				}
				if (skip) {continue;}
				
				
				if (DEPENDENCY) {
					errs() << "Analysing BB: " << "\n";
					errs() << *body << "\n";
				}
				
				for (BasicBlock::iterator I = body->begin(); I!=body->end(); I++) {
					outerLoopIns.push_back(&(*I));
				}
			}
				
				
			for (unsigned int i=0; i<outerLoopIns.size(); i++) {
				for (unsigned int j=i; j<outerLoopIns.size(); j++) {
					Instruction* src = outerLoopIns[i];
					Instruction* dst = outerLoopIns[j];
					if (isa<CallInst>(src) || isa<CallInst>(dst)) {continue;}
					std::unique_ptr<Dependence> d = DI.depends(src, dst, true);
					if (d) {
						if (DEPENDENCY) {errs() << "Depedence between: " << *src << "And " << *dst << "\n";}
						unsigned int l = d->getLevels();
						const SCEV* s = d->getDistance(l);
						if (DEPENDENCY) {errs() << "SCEV object at: " << s << "\n";}
						if (s) {
							if (DEPENDENCY) {errs() << "SCEV: " << *s << "\n";}
							if (DEPENDENCY) {errs() << "SCEV zero: " << s->isZero() << "\n";}
							if (!s->isZero()) {
								return false;
							}
						}
					}
				}
			}
			
			
			if (DEPENDENCY) {errs() << "Dependency: " << noDependency << "\n";}
			return true;
		
		}
		
		
		void getGuardInstructions(Loop* loop) {
			if (DEPENDENCY) {errs() << "Entering getGuardInstructions" << "\n";}
			std::vector<Instruction*> toPutBetween;
			std::vector<Loop*> subLoops = loop->getSubLoops();
			DependenceInfo& DI = getAnalysis<DependenceAnalysisWrapperPass>().getDI();
			std::vector<Instruction*> outerLoopIns;
			
			for (Loop::block_iterator it = loop->block_begin(); it!=loop->block_end(); it++) {
				BasicBlock* body = *it;
				
				bool skip = false;
				for (Loop* l : subLoops) {
					if (l->contains(body)) {
						skip = true;
						break;
					}
				}
				if (skip) {continue;}
				
				
				if (DEPENDENCY) {
					errs() << "Analysing BB: " << "\n";
					errs() << *body << "\n";
				}
				
				for (BasicBlock::iterator I = body->begin(); I!=body->end(); I++) {
					outerLoopIns.push_back(&(*I));
				}
			}
				
			int s = outerLoopIns.size();	
			int prevStart = -1;
			int prevEnd = -1;
			for (int i=0; i<s-1; i++) {
				Instruction* I = outerLoopIns[i];
				
				// Even if no dependence but storeInst exists, we need to lock this within critical section due to killthread signal
			    if (toPutBetween.size() == 0 && isa<StoreInst>(I)) {
			    	int i2 = i+1;
			    	toPutBetween.push_back(I);
					toPutBetween.push_back(outerLoopIns[i2+1]);
					prevStart = i;
					prevEnd = i2;
					continue;
			    }
			    
				for (int i2=i+1; i2<s; i2++) {
					Instruction* I2 = outerLoopIns[i2];
					std::unique_ptr<Dependence> d = DI.depends(I, I2, true);
				    
					if (d) {
						unsigned int l = d->getLevels();
						const SCEV* s = d->getDistance(l);
						if (s && !(s->isZero())) {
							if (DEPENDENCY) {errs() << "Depedence between: " << *I << " AND " << *I2 << "\n";}
							// We have a cross-iteration dependency, so wait() before 'I' and signal after 'I2' (so put inst after I2 in list)
							if (prevStart < 0) {	//First time we're putting wait()
								toPutBetween.push_back(I);
								if (DEPENDENCY) {errs() << "Pushed back: " << *I << "\n";}
								toPutBetween.push_back(outerLoopIns[i2+1]);
								if (DEPENDENCY) {errs() << "Pushed back: " << *(outerLoopIns[i2+1]) << "\n";}
								prevStart = i;
								prevEnd = i2;
								continue;
							}
							
							if (i < prevEnd && i2 <= prevEnd) {
								if (DEPENDENCY) {errs() << "Above dependency already present inside a critical section" << "\n";}
								continue;
							}
							
							else if (i < prevEnd && i2 > prevEnd) {
								// 'I' already in critical section
								// Replace last inst in toPutBetween with I2 and extend previous critical section
								toPutBetween.pop_back();
								if (DEPENDENCY) {errs() << "popped back: " << "\n";}
								toPutBetween.push_back(outerLoopIns[i2+1]);
								if (DEPENDENCY) {errs() << "Pushed back: " << *(outerLoopIns[i2+1]) << "\n";}
								prevEnd = i2;
								continue;
							}
							// Otherwise we insert new critical section
							toPutBetween.push_back(I);
							if (DEPENDENCY) {errs() << "Pushed back: " << *(I) << "\n";}
							toPutBetween.push_back(outerLoopIns[i2+1]);
							if (DEPENDENCY) {errs() << "Pushed back: " << *(outerLoopIns[i2+1]) << "\n";}
							prevStart = i;
							prevEnd = i2;
						}
						
					}
				}
				
				// Printing toPutBetween
				if (DEPENDENCY) {
					errs() << "Printing toPutBetween:" << "\n";
					for(Instruction* i : toPutBetween) {
						errs() << *i << "\n";
					}
				}
				
			}
			this->toPutBetween = toPutBetween;			
		
		}
		
		StructType* insertPthreadFunctions(Module& M) {
			ArrayType* artype = ArrayType::get(Type::getInt8Ty(M.getContext()), 48);
			std::vector<Type*> structTypes;
			structTypes.push_back(Type::getInt64Ty(M.getContext()));
			structTypes.push_back(artype);
			StructType* unionattr = StructType::create(structTypes, "unionattr");
			
			// For threadNum
			Type* pthreadTy = Type::getInt64Ty(M.getContext());
			
			// For function type void* (void*)
			Type* args[] = {Type::getInt8PtrTy(M.getContext())};
			FunctionType* functionCall = FunctionType::get(Type::getInt8PtrTy(M.getContext()), ArrayRef<Type*>(args,1), false);
			
			// List of arguments for pthread_create
			Type* argsPTC[] = {pthreadTy->getPointerTo(), PointerType::get(unionattr, 0), PointerType::get(functionCall, 0), PointerType::get(Type::getInt8Ty(M.getContext()), 0)};
			
			// FunctionType of pthread_create
			FunctionType* pthreadCreateTy = FunctionType::get(Type::getInt32Ty(M.getContext()), ArrayRef<Type*>(argsPTC,4), false);
			
			M.getOrInsertFunction("pthread_create", pthreadCreateTy);
			
			// Insert pthread_join declaration
			Type* argsPTJ[] = {Type::getInt64Ty(M.getContext()), PointerType::get(PointerType::get(Type::getInt8Ty(M.getContext()), 0), 0)};
			FunctionType* pthreadJoinTy = FunctionType::get(Type::getInt32Ty(M.getContext()), ArrayRef<Type*>(argsPTJ,2), false);
			M.getOrInsertFunction("pthread_join", pthreadJoinTy);
			return unionattr;
		}
		
		bool setInstructionsUsingValuesInEntryBlock(std::vector<Value*> values, Loop* loop) {
			std::map<Value*, std::vector<Instruction*>> mapping;
			
			std::vector<BasicBlock*> loopBB = loop->getBlocks();
			
			if (MAPPING) {errs() << "Entering mapping algorithm" << "\n";}
			
			for (Value* i: values) {
				for (Value::user_iterator u =i->user_begin(); u != i->user_end(); u++) {
					User* user = *u;
					Instruction* inst = dyn_cast<Instruction>(user);
					if (loop->contains(inst)) {
						if (!(isa<StoreInst>(inst))) {
							mapping[i].push_back(inst);
						}
						else {	// Iteration stores value into variable, can't parallelise
							if (MAPPING) {errs() << "StoreInst to global variable present" << "\n";}
							return false;
						}
					}
				}
			}
			
			if (MAPPING) {
				for (std::map<Value*, std::vector<Instruction*>>::iterator it=mapping.begin(); it!=mapping.end(); ++it) {
					errs() << "Key:" << *(it->first) << "\n";
					for(auto iii:it->second) {
						errs() << "Value:     " << *iii << "\n";
					}
				}
			}
			if (MAPPING) {errs() << "Finished mapping algorithm" << "\n";}
			this->mapping = mapping;
			
			return true;
		}
		
		
		bool instructionsInsideLoopAreValid(Loop* loop) {
			// Checks that there are no function calls inside loop and no instruction value inside loop is used outside
			for (Loop::block_iterator it = loop->block_begin(); it!=loop->block_end(); it++) {
				BasicBlock* body = *it;
				
				// For all instructions inside loop we check it isn't used outside and that none of it is a function call
				for (BasicBlock::iterator I = body->begin(); I!=body->end(); I++) {
					Instruction* inst = &(*I);
					
					if(CallInst* c = dyn_cast<CallInst>(inst)) { // A function call exists in the outermost loop
						Function* called = c->getCalledFunction();
						if (called && !(called->onlyReadsMemory())) {	// In case 'called' is returned as NULL
							if (OUTPUTT) {errs() << "Function call present in loop accesses memory, can't parallelise" << "\n";}
							return false;
						}
					}
					
					else {
						for (Value::user_iterator u =inst->user_begin(); u != inst->user_end(); u++) {
							User* user = *u;
							Instruction* instUsed = dyn_cast<Instruction>(user);
							if (!(loop->contains(instUsed))) {
								if (OUTPUTT) {errs() << "Value inside loop used outside so can't parallelise" << "\n";}
								return false;
							}
						}
					}
				}
				
			
			}
			
			return true;
		}
		
		StructType* createInnerStructType(Module& M) {
			// Go through mapping variable and create the required StructType
			std::vector<Type*> innerStructTypes;
			for (std::map<Value*, std::vector<Instruction*>>::iterator it=this->mapping.begin(); it!=this->mapping.end(); ++it) {
				
				Value* ins = dyn_cast<Value>(it->first);
				Type* allocaType = ins->getType();
				
				if (DEBUGPHI) {errs() << "Puting type: " << *allocaType << "\n";}
				
				if (AllocaInst* allocainst = dyn_cast<AllocaInst>(it->first)) {
					Type* allocaType = allocainst->getAllocatedType();
					if (ArrayType* ATy = dyn_cast<ArrayType>(allocaType)) {
						innerStructTypes.push_back(PointerType::get(ATy->getArrayElementType(), 0));
					}
					else if (dyn_cast<Instruction>(allocainst->getArraySize())) {
						innerStructTypes.push_back(PointerType::get(allocainst->getAllocatedType(), 0));
					}
					else {
						innerStructTypes.push_back(allocaType);
					}
				}
				
				else {						
					innerStructTypes.push_back(allocaType);
				}
			}
			
			StructType* st = StructType::create(M.getContext(), innerStructTypes, "innerStTy");
			if (DEBUGG) {
				errs() << *st << "\n";
			}
			return st;
		}
		
		StructType* createOuterStructType(Module& M, StructType* innerStTy, Value* iterationStartValue, Value* iterationEndValue, bool DOALL, bool DOACROSS) {
			// outerStruct contains start and end iteration values and pointer to innerStruct of variables
			std::vector<Type*> outerStructTypes;
			
			if (DOACROSS) {
				outerStructTypes.push_back(PointerType::get(Type::getInt32Ty(M.getContext()), 0));	// ThreadLock to wait()
				outerStructTypes.push_back(PointerType::get(Type::getInt32Ty(M.getContext()), 0));	// ThreadLock for signal()
				outerStructTypes.push_back(PointerType::get(Type::getInt32Ty(M.getContext()), 0));	// currThreadKill signal
				outerStructTypes.push_back(PointerType::get(Type::getInt32Ty(M.getContext()), 0));	// nextThreadKill signal
			}
			
			outerStructTypes.push_back(iterationStartValue->getType());		// Iteration start
			outerStructTypes.push_back(iterationEndValue->getType());		// Iteration end (Iteration increment automatically set in pass)
			
			outerStructTypes.push_back(PointerType::get(innerStTy, 0));
			return StructType::create(M.getContext(), outerStructTypes, "outerStTy");
		}
		
		void parseInnerSt(BasicBlock& BB2, LoadInst* innerSt, StructType* innerStTy) {
			
			// The order we fill innerStruct is the same as the keys in mapping order
			std::vector<Value*> index_vector_args;
			index_vector_args.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 0));
			int argCounter = 0;
			// Go through mapping and get GEP for each Key and replace use in Values with Loaded GEP value inside newFn!
			for (std::map<Value*, std::vector<Instruction*>>::iterator it=this->mapping.begin(); it!=this->mapping.end(); ++it) {
				index_vector_args.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), argCounter));
				
				if (DEBUGG) {
					errs() << "INSIDE parseInnerSt" << "\n";
					errs() << "InnerStTy: " << *innerStTy << "\n";
					errs() << "InnerSt: " << *(innerSt->getType()) << "\n";
				}
				
				GetElementPtrInst* gepInst2 = GetElementPtrInst::Create(innerStTy, innerSt, index_vector_args, "InnerStIdx", &(BB2.back()));	// We create GEP for all the elements of inner Struct and replace all Value in mapping with this GEP
				
				Value* ins = dyn_cast<Value>(it->first);
				std::vector<Instruction*> allocaUsedIn = it->second;
				
				LoadInst* intPtr = new LoadInst(gepInst2, "loadedInnerStruct", &(BB2.back()));	// Load the value from struct
				
				for (Instruction* I : allocaUsedIn) {
					if (GetElementPtrInst* existingGEP = dyn_cast<GetElementPtrInst>(I)) {
						if (AllocaInst* allocainst = dyn_cast<AllocaInst>(ins)) {
							if (ArrayType* arrayType = dyn_cast<ArrayType>(allocainst->getAllocatedType())) {
								// If GEP instr accessing ArrayType then need to replace with pointer semantics.
								// Load the value from innerSt int** (gepinst2) into an int* (intPtr)
								// Use new GEP that accesses this int*
							
								Type* arrayElemType = arrayType->getArrayElementType();
								std::vector<Value*> arrayAccessIndices;
								for (GetElementPtrInst::op_iterator GEPt=existingGEP->idx_begin(); GEPt!=existingGEP->idx_end(); ++GEPt) {
									arrayAccessIndices.push_back(*GEPt);
								}
								arrayAccessIndices.erase(arrayAccessIndices.begin());	// Remove the 0th element
								
								if (DEBUGG) {
								errs() << I << "\n";
									errs() << "Key: " << *ins << "\n";
									errs() << "used in: " << *I << "\n";
									errs() << *(I->getParent()) << "\n";
								
									for (Value::user_iterator u =I->user_begin(); u != I->user_end(); u++) {
										errs() << "User" << **u << "\n";
									}
								
								}

								GetElementPtrInst* newGEP=GetElementPtrInst::Create(arrayElemType, intPtr, arrayAccessIndices, "InnerStArr", I);

								I->replaceAllUsesWith(newGEP);
								
								I->eraseFromParent();
								
								if (DEBUGG) {errs() << "After" << *(newGEP->getParent()) << "\n";}
								
								continue;
							}
						}
						
					}
					//For all other innerSt, these values don't change. So load at entry: block. For array too we load in entry:
					if (LoadInst* loadedAlloca = dyn_cast<LoadInst>(I)) {
						for (auto* user:loadedAlloca->users()) {
							user->replaceUsesOfWith(loadedAlloca, intPtr);
						}
						loadedAlloca->eraseFromParent();
					}
					else {
						I->replaceUsesOfWith(ins, intPtr);
					}
				}
				argCounter++;
				index_vector_args.pop_back();
			}
			
		}
		
		AllocaInst* populateInnerStInOldFunction(BasicBlock& BB2, StructType* innerStTy, Instruction& toAddBefore) {
			AllocaInst* innerStOldFn = new AllocaInst(innerStTy, "innerStOldFn", &toAddBefore);
			std::vector<Value*> index_args;
			index_args.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 0));
			int argCounter = 0;
			
			// Go through mapping and get GEP for each Key in mapping (this will be an entry in innerstruct) and store the required value in inner struct
			for (std::map<Value*, std::vector<Instruction*>>::iterator it=this->mapping.begin(); it!=this->mapping.end(); ++it) {
				index_args.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), argCounter));
				// We create GEP for all the elements of inner Struct and replace all Value in mapping with this GEP
				GetElementPtrInst* gepInstInner = GetElementPtrInst::Create(innerStTy, innerStOldFn, index_args, "InnerStIdx", &toAddBefore);
				
				if (AllocaInst* allocainst = dyn_cast<AllocaInst>(it->first)) {
					if (ArrayType* ATy = dyn_cast<ArrayType>(allocainst->getAllocatedType())) {
						std::vector<Value*> gepidx;
						gepidx.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 0));
						gepidx.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 0));
						GetElementPtrInst* tempLoad = GetElementPtrInst::Create(ATy, allocainst, gepidx, "ArrayPtr", &toAddBefore);
						new StoreInst(tempLoad, gepInstInner, &toAddBefore);
					}
					else if (dyn_cast<Instruction>(allocainst->getArraySize())) {
							std::vector<Value*> gepidx;
							gepidx.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 0));
							Type* elemType = allocainst->getAllocatedType();
							if (DEBUGG) {
								errs() << "Type: " << *elemType << "\n";
							}
							GetElementPtrInst* tempLoad = GetElementPtrInst::Create(elemType, allocainst, gepidx, "ArrayPtr", &toAddBefore);
							new StoreInst(tempLoad, gepInstInner, &toAddBefore);
						}
						else {
							// To store in memory pointed by GEP, we first load the value and then use this in StoreInst, can only store loaded values!!!
							LoadInst* tempLoad = new LoadInst(allocainst, "loadingValue", &toAddBefore);
							new StoreInst(tempLoad, gepInstInner, &toAddBefore);
						}
				}
				else {
					Value* v = dyn_cast<Value>(it->first);
					new StoreInst(v, gepInstInner, &toAddBefore);
				}
				
				argCounter++;
				index_args.pop_back();
			}
			
			return innerStOldFn;
		}
		
		AllocaInst* populateOuterStInOldFunction (StructType* outerStTy, Value* iterStart, Value* iterEnd, LoadInst* loadedInnerStPtrOldFn, BasicBlock& BB2, Instruction& toAddBefore) {
			// FOR DOALL
			if (DEBUGPHI) {errs() << *outerStTy << "\n";}
			
			AllocaInst* outerStOldFn = new AllocaInst(outerStTy, "outerStOldFn", &toAddBefore);
			std::vector<Value*> index_args2;
			index_args2.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 0));
			index_args2.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 0));
			GetElementPtrInst* gepInstOuter0 = GetElementPtrInst::Create(outerStTy, outerStOldFn, index_args2, "OuterStIdx", &toAddBefore);
			
			new StoreInst(iterStart, gepInstOuter0, &toAddBefore);	// Store starting value of iteration
			index_args2.pop_back();
		
			index_args2.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 1));
			GetElementPtrInst* gepInstOuter1 = GetElementPtrInst::Create(outerStTy, outerStOldFn, index_args2, "OuterStIdx", &toAddBefore);
			
			new StoreInst(iterEnd, gepInstOuter1, &toAddBefore);	// Store end value of iteration
			index_args2.pop_back();
		
			index_args2.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 2));
			GetElementPtrInst* gepInstOuter2 = GetElementPtrInst::Create(outerStTy, outerStOldFn, index_args2, "OuterStIdx", &toAddBefore);
			
			new StoreInst(loadedInnerStPtrOldFn, gepInstOuter2, &toAddBefore);
			return outerStOldFn;
		}
		
		
		AllocaInst* populateOuterStInOldFunction (StructType* outerStTy, AllocaInst* waitLoc, AllocaInst* signalLoc, AllocaInst* currThreadKill, AllocaInst* nextThreadKill, Value* iterStart, Value* iterEnd, LoadInst* loadedInnerStPtrOldFn, BasicBlock& BB2, Instruction& toAddBefore) {
			//FOR DOACROSS
			if (DEBUGPHI) {errs() << *outerStTy << "\n";}
			
			AllocaInst* outerStOldFn = new AllocaInst(outerStTy, "outerStOldFn", &toAddBefore);
			std::vector<Value*> index_args2;
			index_args2.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 0));
			
			index_args2.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 0));
			GetElementPtrInst* gepInstOuter0 = GetElementPtrInst::Create(outerStTy, outerStOldFn, index_args2, "OuterStIdx", &toAddBefore);
			new StoreInst(waitLoc, gepInstOuter0, &toAddBefore);	// Store wait() signal thread lock
			index_args2.pop_back();
			
			index_args2.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 1));
			GetElementPtrInst* gepInstOuter1 = GetElementPtrInst::Create(outerStTy, outerStOldFn, index_args2, "OuterStIdx", &toAddBefore);
			new StoreInst(signalLoc, gepInstOuter1, &toAddBefore);	// Store signal() value
			index_args2.pop_back();
			
			index_args2.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 2));
			GetElementPtrInst* gepInstOuter2 = GetElementPtrInst::Create(outerStTy, outerStOldFn, index_args2, "OuterStIdx", &toAddBefore);
			new StoreInst(currThreadKill, gepInstOuter2, &toAddBefore);	// Store currThreadKill value
			index_args2.pop_back();
			
			index_args2.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 3));
			GetElementPtrInst* gepInstOuter3 = GetElementPtrInst::Create(outerStTy, outerStOldFn, index_args2, "OuterStIdx", &toAddBefore);
			new StoreInst(nextThreadKill, gepInstOuter3, &toAddBefore);	// Store nextThreadKill value
			index_args2.pop_back();
			
			index_args2.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 4));
			GetElementPtrInst* gepInstOuter4 = GetElementPtrInst::Create(outerStTy, outerStOldFn, index_args2, "OuterStIdx", &toAddBefore);
			new StoreInst(iterStart, gepInstOuter4, &toAddBefore);	// Store start value of iteration
			index_args2.pop_back();
			
			
			index_args2.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 5));
			GetElementPtrInst* gepInstOuter5 = GetElementPtrInst::Create(outerStTy, outerStOldFn, index_args2, "OuterStIdx", &toAddBefore);
			new StoreInst(iterEnd, gepInstOuter5, &toAddBefore);	// Store end value of iteration
			index_args2.pop_back();
			
		
			index_args2.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 6));
			GetElementPtrInst* gepInstOuter6 = GetElementPtrInst::Create(outerStTy, outerStOldFn, index_args2, "OuterStIdx", &toAddBefore);
			new StoreInst(loadedInnerStPtrOldFn, gepInstOuter6, &toAddBefore);
			return outerStOldFn;
		}
		
		void insertWait(Value* killSemaphore, Value* lockSemaphore, Instruction* insertBefore, Function* F) {
			/* 
			Below is code to insert wait() method before toPutWait
			- AtomicCmpXchgInst Returns the value that was loaded.
			*/
			
			// Split existing BB to before and after CS
			BasicBlock* parentBB = insertBefore->getParent();
			BasicBlock* csBB = parentBB->splitBasicBlock(insertBefore, "criticalSection");
			BasicBlock* endOfFn = &(F->back());
			
			// Create BB for checking if need to quit thread
			BasicBlock* threadKillSpin = BasicBlock::Create(F->getContext(), "threadKillChk", F, csBB);
			BranchInst* b = dyn_cast<BranchInst>(parentBB->getTerminator());
			b->setSuccessor(0, threadKillSpin);
			
			// Create new BB for one-time check when kill signal sent, spining when kill not sent and atomic compare and exchange spin
			BasicBlock* loadCheck = BasicBlock::Create(F->getContext(), "loadCheck", F, csBB);
			BasicBlock* loadSpin = BasicBlock::Create(F->getContext(), "loadSpin", F, csBB);
			BasicBlock* atomicRMWSpin = BasicBlock::Create(F->getContext(), "atomicRMW", F, csBB);
			
			// Read value from killSemaphore and see if < 0
			Value* loadedKillValue = new LoadInst(killSemaphore, "loadingKillValue", threadKillSpin);	// Doesn't need to be atomic 
			Value* zero = ConstantInt::getSigned(Type::getInt32Ty(F->getContext()), 0);
			ICmpInst* cond = new ICmpInst(*threadKillSpin, llvm::CmpInst::Predicate::ICMP_SLT, loadedKillValue, zero, "killCond");//SemValue<0
			BranchInst::Create(loadCheck, loadSpin, cond, threadKillSpin); // Branch to atomicxchgSpin at end of loadSpin if successful
			
			// Check lockSemaphore value to see if set to 1 after kill sent
			Value* loadedSemValue = new LoadInst(lockSemaphore, "loadingSemValue", loadCheck);	// Doesn't need to be atomic 
			ICmpInst* cond2 = new ICmpInst(*loadCheck, llvm::CmpInst::Predicate::ICMP_SGT, loadedSemValue, zero, "lockCond");//SemValue>0
			BranchInst::Create(atomicRMWSpin, endOfFn, cond2, loadCheck); // Branch to atomicxchgSpin at end of loadSpin if successful
			
			// If killSemaphore == 0, then we do normal spin lock check
			Value* loadedSemValue2 = new LoadInst(lockSemaphore, "loadingSemValue", loadSpin);	// Doesn't need to be atomic 
			ICmpInst* cond3 = new ICmpInst(*loadSpin, llvm::CmpInst::Predicate::ICMP_SGT, loadedSemValue2, zero, "lockCond");//SemValue>0
			BranchInst::Create(atomicRMWSpin, threadKillSpin, cond3, loadSpin); // Branch to atomicxchgSpin at end of loadSpin if successful
			
			// Create new BB for atomic compare and exchange spin
			IRBuilder<> builder(atomicRMWSpin);
			Value* one = ConstantInt::getSigned(Type::getInt32Ty(F->getContext()), 1);
			builder.CreateAtomicRMW(llvm::AtomicRMWInst::BinOp::Sub, lockSemaphore, one, order, syncScope);
			// Above is fine since only one thread will ever decrement the value and atomically so too. So after checking if > 0, mem value 
			// can only be increased by another thread. Even if so this can happen without any issue.
			builder.CreateBr(csBB);
			
		}
		
		void insertSignal(Value* semaphore, Instruction* insertBefore, Function* F) {
			Value* one = ConstantInt::getSigned(Type::getInt32Ty(F->getContext()), 1);
			new AtomicRMWInst(llvm::AtomicRMWInst::BinOp::Add, semaphore, one, order, syncScope, insertBefore);
			
		}
		
		void insertKill(Value* semaphore, Instruction* insertBefore, Function* F) {
			// At the last BasicBlock, when we reach here through normal termination or kill signal we pass message onto other threads
			BasicBlock* endOfFn = &(F->back());
			Value* minusOne = ConstantInt::getSigned(Type::getInt32Ty(F->getContext()), -1);
			new AtomicRMWInst(llvm::AtomicRMWInst::BinOp::Xchg, semaphore, minusOne, order, syncScope, &(endOfFn->back()));
			
		}
		
		
		virtual bool runOnFunction(Function& F) {
			Module& M = *(F.getParent());
			
			// Condition to stop pass running on newly created parallelised functions
			if (F.getName().startswith("ParallelisedLoop")) {
				return false;
			}
			
			if (OUTPUTT) {errs() << "Optimisation being run on function: " << F.getName() << "\n";}
			if (OUTPUTT) {errs();}
			
			LoopInfo& LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();	// Returns info about all loops in function
		
			for (LoopInfo::iterator LIT = LI.begin(); LIT != LI.end(); LIT++) {
				if (OUTPUTT) {errs() << "Starting new loop iteration analysis" << "\n" << "\n";}
				Loop* loop = *LIT;
				
				if (loop->getLoopDepth() != 1) {continue;}
				
				bool DOALL = true;
				bool DOACROSS = false;
				
				
				bool safeToParallelise = this->hasNoDependencies(loop); // 1 if no dependency, 0 if there are dependencies
				if (OUTPUTT) {errs() << "Safe: " << (safeToParallelise) << "\n";}
				
				if (!safeToParallelise) {
					DOALL = false;
					DOACROSS = true;
					this->getGuardInstructions(loop);
				}
				
				
				if (OUTPUTT) {errs() << "DOALL: " << DOALL << "\n";}
				if (OUTPUTT) {errs() << "DOACROSS: " << DOACROSS << "\n";}
				
				PHINode* phi = loop->getCanonicalInductionVariable();
				
				if (phi) { 
					if (OUTPUTT) {errs() << *(loop->getCanonicalInductionVariable()) << "\n";}
				} 
				else {
					if (OUTPUTT) {errs() << "Phi node was returned as null" << "\n";}
					
					for (BasicBlock* BB : loop->getBlocks()) {
						if (PHINode* p = dyn_cast<PHINode>(&(BB->front()))) {
							phi = p;
							if (OUTPUTT) {errs() << "Phi node we guess to be: " << *phi << "\n";}
							break;
						}
					}
				
				}
				
				if (!phi) {
					if (OUTPUTT) {errs() << "We could not guess phi, so cannot parallelise" << "\n";}
					continue;
				}
					
				
				
				/* Before we change Itervation variables in loop to read from outer Struct, we need to know if SCEV anaysis is possible */
				std::vector<ConstantInt*> startValues;
				std::vector<ConstantInt*> endValues;
				ScalarEvolution& SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
				if (!SE.isSCEVable(phi->getType())) {
					if (OUTPUTT) {errs() << "Phi not SCEV-able" << "\n";}
					continue;
				}
				const SCEV* scev = SE.getSCEV(phi);
				
				bool SCEVfailed = false;
				
				unsigned int totalIterations = SE.getSmallConstantTripCount(loop);
				if (totalIterations == 0) {
					if (OUTPUTT) {errs() << "Total iterations of loop said to be 0, can't parallelise" << "\n";}
					SCEVfailed = true;
					continue;
				}
				if (DEBUGG) {errs() << "totalIterations; " << totalIterations << "\n";}
				unsigned int perThread = (totalIterations / this->core_count) + 1;	// So each thread atleast does 1 iteration, worst case we spawn and then quit.
				if (DEBUGG) {errs() << "perThread; " << perThread << "\n";}
				
				for (unsigned int i=0; i<this->core_count; i++) {
					if(const SCEVAddRecExpr* exp =dyn_cast<SCEVAddRecExpr>(scev)) {
						if (DOACROSS) {
							
							if ((i+1) > totalIterations) {
								break;	// Even if more threads available, we stop after we exhaust all iterations
							}
							
							ConstantInt* i_th = ConstantInt::getSigned(Type::getInt32Ty(F.getContext()), i);
							const SCEV* i_th_scev = SE.getConstant(i_th);
							const SCEV* startValue = exp->evaluateAtIteration(i_th_scev, SE);
							const SCEVConstant* startValueConstant = dyn_cast<SCEVConstant>(startValue);
							if (!startValueConstant) {SCEVfailed = true; break;}
							ConstantInt* c = startValueConstant->getValue(); 
							startValues.push_back(c);
						}
						
						if (DOALL) {	//DOALL
							if (i * perThread >= totalIterations) {
								break;
							}
							ConstantInt* i_th = ConstantInt::getSigned(Type::getInt32Ty(F.getContext()), (i * perThread));
							const SCEV* i_th_scev = SE.getConstant(i_th);
							const SCEV* startValue = exp->evaluateAtIteration(i_th_scev, SE);
							const SCEVConstant* startValueConstant = dyn_cast<SCEVConstant>(startValue);
							if (!startValueConstant) {SCEVfailed = true; break;}
							ConstantInt* cStart = startValueConstant->getValue(); 
							if (DEBUGG) {errs() << "Start Value; " << *cStart << "\n";}
							startValues.push_back(cStart);
							
							ConstantInt* i_th_end = ConstantInt::getSigned(Type::getInt32Ty(F.getContext()), ((i+1) * perThread));
							const SCEV* i_th_end_scev = SE.getConstant(i_th_end);
							const SCEV* endValue = exp->evaluateAtIteration(i_th_end_scev, SE);
							const SCEVConstant* endValueConstant = dyn_cast<SCEVConstant>(endValue);
							if (!endValueConstant) {SCEVfailed = true; break;}
							ConstantInt* cEnd = endValueConstant->getValue(); 
							if (DEBUGG) {errs() << "End Value; " << *cEnd << "\n";}
							
							ConstantInt* last = ConstantInt::getSigned(Type::getInt32Ty(F.getContext()), totalIterations);
							const SCEV* last_scev = SE.getConstant(last);
							const SCEV* lastValue = exp->evaluateAtIteration(last_scev, SE);
							const SCEVConstant* lastConstant = dyn_cast<SCEVConstant>(lastValue);
							if (!lastConstant) {SCEVfailed = true; break;}
							ConstantInt* cLast = lastConstant->getValue(); 
							if (DEBUGG) {errs() << "Last Value: " << *cLast << "\n";}
							
							if ((i+1) * perThread > totalIterations) {	// To prevent iteration end value being set too high/low
								endValues.push_back(cLast);
							}
							else {
								endValues.push_back(cEnd);
							}
							
							
						}
					}
					else {
						if (OUTPUTT) {errs() << "For phi: " << *phi << "\n";}
						if (OUTPUTT) {errs() << "CAN'T PREDICT HOW INDUCTION VARIABLE EVOLVES!!!" << "\n";}
						SCEVfailed = true;
						break;
					}
				}
				
				if (SCEVfailed) {
					if (OUTPUTT) {errs() << "SCEV Failed" << "\n";}
					continue;
				}
				
				bool valid = this->instructionsInsideLoopAreValid(loop);	// For DOALL and DOACROSS, no function call that changed memory and no reassigning variables stored outside
				
				if (!valid) {
					continue;
				}
				
				unsigned int thread_count = startValues.size();
				
				BasicBlock* prev = loop->getLoopPreheader();	//Might be entry BB or separate preheader BB
				if (!prev) {
					prev = loop->getLoopPredecessor();
				}
				
				BasicBlock& entryBB = *prev;
				
				
				// We pass all instructions to be checked if used as Loop as Values: entry: preheader: and function argument
				std::vector<Value*> valuesToCheckIfUsedInLoop;
				
				// Get all insts before loop and check whether they're value used inside loop				
				for (BasicBlock& BB : F.getBasicBlockList()) {
					if (loop->contains(&BB)) {
						break;
					}
					if (DEBUGG) {errs() << "Putting insts from BB: " << BB << "\n";}
					for (Instruction& i : BB.getInstList()) {
						valuesToCheckIfUsedInLoop.push_back(dyn_cast<Value>(&i));
					}
				}
				
				// Push any function arguments into this vector
				for (Argument& a: F.getArgumentList()) {
					if (DEBUGG) {
						errs() << "Argument: " << a << "\n";
						errs() << "Argument Type: " << *(a.getType()) << "\n";
					}
					valuesToCheckIfUsedInLoop.push_back(dyn_cast<Value>(&a));
				}
				
				
				bool noStoreInst = this->setInstructionsUsingValuesInEntryBlock(valuesToCheckIfUsedInLoop, loop); //Set variable mapping			
					
				if (!noStoreInst) {		// Can't parallelise loops which stores to global variable in each iteration
					if (OUTPUTT) {errs() << "Can't parallelise loop since store inst" << "\n";}
					continue;
				}
				
				// Remove BB of loop from parent Function and move into new function 
				// Create new function of type: void* newFn(void*) to call from pthread_create
				Type* fnArgs[] = {Type::getInt8PtrTy(M.getContext())};
				FunctionType* newFnType = FunctionType::get(Type::getInt8PtrTy(M.getContext()), ArrayRef<Type*>(fnArgs,1), false);
				std::string functionName = "ParallelisedLoop" + std::to_string(this->counter);
				this->counter++;
				Constant* newFnn = M.getOrInsertFunction(functionName, newFnType);
				Function* newFn = dyn_cast<Function>(newFnn);
				
				//NewFn has now entry: and end: blocks
				BasicBlock* newFnBBEntry = BasicBlock::Create(M.getContext(), "entry");	// Add terminator then insert
				BasicBlock* newFnBBEnd = BasicBlock::Create(M.getContext(), "end");	// Add terminator then insert
				Constant* n = Constant::getNullValue(Type::getInt8PtrTy(M.getContext()));
				ReturnInst::Create(M.getContext(), n, newFnBBEnd);
				newFnBBEntry->insertInto(newFn);
				newFnBBEnd->insertInto(newFn);
				
				// Remove BasicBlocks from original function (and see if below mapping code still works)
				Instruction* iterationVar;	// The iteration Instruction
				std::vector<Instruction*> iterationVarUsed;	// The list of instructions using iteration variable
				Value* iterationEndValue = NULL;	// The highest iteration value to compare against
				CmpInst* iterationEndValueUsed = NULL;
				
				BasicBlock* endOfOldFnBlock = loop->getUniqueExitBlock();
				bool noCmpInstFound = false;
				
				for (Value::user_iterator u =endOfOldFnBlock->user_begin(); u != endOfOldFnBlock->user_end(); u++) {
					User* user = *u;	// User of endOfOldFnBlock as an operand for instruction
					Instruction* inst = dyn_cast<Instruction>(user);
					if (inst) {	// inst not null
						if (loop->contains(inst)) {
							// inst is the branch %exit.cond %branch1 %branch2 
							BranchInst* b1 = dyn_cast<BranchInst>(inst);
							iterationEndValueUsed = dyn_cast<CmpInst>(b1->getCondition());
							if (iterationEndValueUsed) {
								iterationEndValue = iterationEndValueUsed->getOperand(1);
							}
							else {
								noCmpInstFound = true;
								break;
							}
							
							// Remove all references to end: in oldFn and replace with end: in newFn
							inst->replaceUsesOfWith(endOfOldFnBlock, newFnBBEnd);	
							
							// Remove iteration variable from mapping if present
							if (Instruction* key = dyn_cast<Instruction>(iterationEndValue)) {
								this->mapping.erase(key);
							}
							
							Instruction& lastInstr = entryBB.back();
							BranchInst* lastBInstr = dyn_cast<BranchInst>(&lastInstr);
							lastBInstr->setSuccessor(0, endOfOldFnBlock);			// Change OldFn entry: last instr to jump to it's end BB
							BranchInst::Create(loop->getHeader(), newFnBBEntry); 	//In entry: for newFn, branch to newly copied for.cond/initial loop BB (variable b)
							
							unsigned int successors = b1->getNumSuccessors();
							if (successors == 1) {
								if (DEBUGPHI) {
									errs() << "Only one successor in branch of 1st BB of loop" << "\n";
								}
							}
							
							else if (successors == 2) {
								if (b1->getSuccessor(1) == endOfOldFnBlock) {
									b1->setSuccessor(1, newFnBBEnd);	// Set for.cond 2nd branch to newFn end: BB
								}
								
								else if (b1->getSuccessor(0) == endOfOldFnBlock) {
									b1->setSuccessor(0, newFnBBEnd);	// Set for.cond 2nd branch to newFn end: BB
								}
							}
						}
					}
				}
				
				if (noCmpInstFound) {
					if (OUTPUTT) {errs() << "No CmpInst found for branch, so must be true/false and only 1 iteration loop" << "\n";}
					newFn->eraseFromParent();
					this->counter--;
					continue;
				}
				
				// These below two cannot be assumed to be always in right order
				int preHeader = 0;
				int backEdge = 1;
				// prev is the BB from which we enter loop
				if (phi->getIncomingBlock(1) == prev) {
					preHeader = 1;
					backEdge = 0;
				}
				
				phi->setIncomingBlock(preHeader, newFnBBEntry);
	
				if (DEBUGPHI){
					errs() << "Exit block: " << *endOfOldFnBlock << "\n";
					errs() << "Iteration EndValue: " << iterationEndValue << "\n";
					errs() << "Iteration EndValueUsed: " << *iterationEndValueUsed << "\n";	
				}
				
				
				for (auto it=loop->block_begin(); it!=loop->block_end(); ++it) {
					BasicBlock* b = *it;
					b->removeFromParent();
					b->insertInto(newFn, newFnBBEnd);
				}
				
				// If any other PHINodes which has oldFn BB, needed as some BB have 2 PHINodes, below works for n PHINodes at start
				PHINode* nextInst = phi;
				// errs() << "nextInst: " << *(prev) << "\n";
				while (nextInst->getNextNode()) {
					nextInst = dyn_cast<PHINode>(nextInst->getNextNode());
					// errs() << "nextInst: " << *nextInst << "\n";
					if (nextInst) {
						if (OUTPUTT) {errs() << "nextInst: " << *nextInst << "\n";}
						if (nextInst->getIncomingBlock(1) == prev) {
							nextInst->setIncomingBlock(1, newFnBBEntry);
						}
						else {
							nextInst->setIncomingBlock(0, newFnBBEntry);
						}
						if (OUTPUTT) {errs() << "nextInst: " << *nextInst << "\n";}
						
					}
					else {break;}
				}
				
				
				if (DEBUGPHI) {
					errs() << F << "\n";
					errs();
					errs() << *newFn << "\n";
				}
				
				// Now we use mapping and taking newFn's argument to deref the struct. We first need to create a struct type globally
				// And also change iteration range
				BasicBlock& BB2 = newFn->getEntryBlock();
				
				// innerStructTypes variable in prev for loop
				StructType* innerStTy = this->createInnerStructType(M); 
				
				// outerStruct contains start and end iteration values and pointer to innerStruct of variables
				Value* iterationStartValue = phi->getIncomingValue(preHeader);
				StructType* outerStTy = this-> createOuterStructType(M, innerStTy, iterationStartValue, iterationEndValue, DOALL, DOACROSS); 
			
				// Change newFn argument to outer struct* type					
				auto& newFnArg = (newFn->getArgumentList()).front();
				BitCastInst* outerSt = new BitCastInst(&newFnArg, PointerType::get(outerStTy, 0), "CastToOuterSt", &(BB2.back()));
				
				// storeOuterSt now contains the outer Struct we need. Now use GEP to get inner Struct
				std::vector<Value*> index_vector;
				index_vector.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 0));//Only one 0 even for accessing ptr
				if (DOALL) {index_vector.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 2));}
				else {index_vector.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 6));}	//DOACROSS
				GetElementPtrInst* gepInst = GetElementPtrInst::Create(outerStTy, outerSt, index_vector, "OuterStIdx", &(BB2.back()));
				LoadInst* innerSt = new LoadInst(gepInst, "innerSt", &(BB2.back()));
				
				
				// Get GEP for innerSt values and insert them end of entry: BB in newFn
				this->parseInnerSt(BB2, innerSt, innerStTy);
				if (DEBUGG) {
					errs() << BB2 << "\n";
				}
				
				
				std::vector<Value*> index_vector_args;
				index_vector_args.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 0));
				
				// GEP for iteration variable
				if (DOALL) {index_vector_args.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 0));}
				else {index_vector_args.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 4));}
				GetElementPtrInst* gepInstIter = GetElementPtrInst::Create(outerStTy, outerSt, index_vector_args, "OuterStItrStart", &(BB2.back()));
				LoadInst* loadedIterVarStart = new LoadInst(gepInstIter, "iterVarStart", &(BB2.back()));
				index_vector_args.pop_back();
				
				if (DOALL) {index_vector_args.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 1));}
				else {index_vector_args.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 5));}
				GetElementPtrInst* gepInsItrEnd = GetElementPtrInst::Create(outerStTy, outerSt, index_vector_args, "OuterStItrEnd", &(BB2.back()));
				LoadInst* loadedIterVarEnd = new LoadInst(gepInsItrEnd, "iterVarEnd", &(BB2.back()));
				index_vector_args.pop_back();
				
				
				
				if (DOACROSS) { 
				
					// GEP for ThreadLock mem locations
					index_vector_args.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 0));
					GetElementPtrInst* gepInstWait = GetElementPtrInst::Create(outerStTy, outerSt, index_vector_args, "OuterStWait", &(BB2.back()));
					LoadInst* loadedThreadWait = new LoadInst(gepInstWait, "ThreadWait", &(BB2.back()));
					index_vector_args.pop_back();
				
					index_vector_args.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 1));
					GetElementPtrInst* gepInstSgnl = GetElementPtrInst::Create(outerStTy, outerSt, index_vector_args, "OuterStSgnl", &(BB2.back()));
					LoadInst* loadedThreadSignal = new LoadInst(gepInstSgnl, "ThreadSignal", &(BB2.back()));
					index_vector_args.pop_back();
				
					index_vector_args.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 2));
					GetElementPtrInst* gepThrdKill = GetElementPtrInst::Create(outerStTy, outerSt, index_vector_args, "OuterStCurrKil", &(BB2.back()));
					LoadInst* loadedCurrThreadKill = new LoadInst(gepThrdKill, "currThreadKill", &(BB2.back()));
					index_vector_args.pop_back();
				
					index_vector_args.push_back(ConstantInt::getSigned(Type::getInt32Ty(BB2.getContext()), 3));
					GetElementPtrInst* gepnxtThrdKill = GetElementPtrInst::Create(outerStTy, outerSt, index_vector_args, "OuterStNxtKil", &(BB2.back()));
					LoadInst* loadedNextThreadKill = new LoadInst(gepnxtThrdKill, "nextThreadKill", &(BB2.back()));
					index_vector_args.pop_back();
				
				
					// Dataflow analysis when multiple paths exist and we need to add synchronisation across all paths using arrays
					if (MAPPING) {errs() << "\n"; errs() << "Entering data flow analysis" << "\n"; errs() << "\n";}
					DominatorTree& DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
					DT.recalculate(*newFn);	// Since we are using newFn which didn't exist before
					std::vector<BasicBlock*> newWaitGuards;
					std::vector<BasicBlock*> newSignalGuards;
					if (OUTPUTT) {errs() << "IN data flow analysis" << "\n";}
					if (OUTPUTT) {errs() << "EXIT NODE FOR newFN: " << newFn->back() << "\n";}
					for (unsigned int i=0; i < toPutBetween.size(); i+=2) {
						Instruction* I = toPutBetween[i];
						BasicBlock* currentBB = I->getParent();
						// errs() << "Parent: " << *parent << "\n";
						std::queue<BasicBlock*> parents;
						parents.push(currentBB);
						
						while(!parents.empty()) {
							BasicBlock* currBB = parents.front();
							if (DT.properlyDominates(currBB, &(newFn->back()))) {
								if (MAPPING) {errs() << "BasicBlock for wait: " << *currBB << " properly dominates exit" << "\n";}
								if (std::find(newWaitGuards.begin(), newWaitGuards.end(), currBB) == newWaitGuards.end()) {
									// Add wait() at end of this (currBB) BasicBlock if it isn't already in list
									newWaitGuards.push_back(currBB);
								}
								break;
							}
							else {
								parents.pop();
								for (BasicBlock* Pred : predecessors(currBB)) {
									parents.push(Pred);	// Eventually we will reach start of function and so will terminate
								}
								
							}
						}
						
						std::queue<BasicBlock*> children;
						children.push(currentBB);
						
						while(!children.empty()) {
							BasicBlock* currBB = children.front();
							if (currBB == &(newFn->back()) || DT.properlyDominates(currBB, &(newFn->back()))) {
								if (MAPPING) {errs() << "BasicBlock for signal: " << *currBB << " properly dominates exit" << "\n";}
								if (std::find(newSignalGuards.begin(), newSignalGuards.end(), currBB) == newSignalGuards.end()) {
									// Add signal() at front of this (currBB) BasicBlock if it isn't already in list
									newSignalGuards.push_back(currBB);
								}
								break;
							}
							else {
								children.pop();
								for (BasicBlock* Succ : successors(currBB)) {
									children.push(Succ);	// Eventually we will reach end of function and so will terminate
								}
								
							}
							
						
						}
						
						// Add appropriate wait() and signal() in all BBs from above lists. Add signal at top of BB and wait at bottom!!!
						
						this->toPutBetween = {};
						for (unsigned int i=0; i<newWaitGuards.size(); i++) {
							BasicBlock* toAddWait = newWaitGuards[i];
							BasicBlock* toAddSignal = newSignalGuards[i];
							
							this->toPutBetween.push_back(&(toAddWait->back()));
							this->toPutBetween.push_back(toAddSignal->getFirstNonPHI());
							
						}
						
						
					}
					
					
					// The loop puts the necessary wait() and signal() before and after the critical sections in newFn
					for (unsigned int vecLen=0; vecLen < toPutBetween.size(); vecLen+=2) {
						Instruction* toPutWait = toPutBetween[vecLen];
						Instruction* toPutSignal = toPutBetween[vecLen+1];
						if (DEPENDENCY) {errs() << "toPutBetween.size():= " << toPutBetween.size() << "\n";}
						if (DEPENDENCY) {errs() << "toPutWait:= " << toPutWait << "\n";}
						if (DEPENDENCY) {if (toPutWait) {errs() << "toPutWait:= " << *toPutWait << "\n";}}
						
						if (DEPENDENCY) {errs() << "toPutSignal:= " << toPutSignal << "\n";}
						if (DEPENDENCY) {if (toPutSignal) {errs() << "toPutSignal:= " << *toPutSignal << "\n";}}
						
						this->insertWait(loadedCurrThreadKill, loadedThreadWait, toPutWait, newFn);	//GEP stored ptr to ptr of ThreadLock, so we load pointer address
						this->insertSignal(loadedThreadSignal, toPutSignal, newFn);
						if (vecLen == 0) {	// We only need to insert it once
							this->insertKill(loadedNextThreadKill, toPutSignal, newFn);
						}
					
					}
				}
				
				// Change induction variabe increment to match with core_count
				Value* threadCount = ConstantInt::get(iterationStartValue->getType(), thread_count);
				Value* incomingValue = phi->getIncomingValue(backEdge);
				BasicBlock* incomingBlock = phi->getIncomingBlock(backEdge);
				Instruction* incomingValueInst = dyn_cast<Instruction>(incomingValue);
					
				Instruction* inductionVarExitCond;
				
				//Below loop ensures the last value we come across that uses incomingValueInst will be stored here as ExitCond
				for (inst_iterator I = inst_begin(newFn), E = inst_end(newFn); I != E; ++I) {
					if (CmpInst* comp = dyn_cast<CmpInst>(&(*I))) {
						// errs() << "Value: " << *comp << "\n";
						if(comp->getOperand(0) == incomingValueInst) {
							// errs() << "Comp: " << *comp << "\n";
							inductionVarExitCond = comp;
						}
					}
				}
					
					
				if (DOACROSS) {	
					Instruction* incomingValueCopy = incomingValueInst->clone();	// Since incomingValueInst may be used elsewher as is
					incomingValueCopy->insertBefore(&(incomingBlock->back()));
					if (incomingValueCopy->isBinaryOp()) {
						Value* currentInc = incomingValueCopy->getOperand(1);
						IRBuilder<> b(incomingValueCopy);
						Value* newInc = b.CreateMul(currentInc, threadCount, "newIterInc", true, true);
						incomingValueCopy->setOperand(1, newInc);
						phi->setIncomingValue(backEdge, incomingValueCopy);
						
						if (DEBUGG) {errs() << "Exit cond: " << *inductionVarExitCond << "\n";}
						// We change exit cond check to use the updated induction increment variable
						inductionVarExitCond->removeFromParent();
						inductionVarExitCond->insertAfter(incomingValueCopy);
						inductionVarExitCond->setOperand(0, incomingValueCopy);
						
					}
					else {
						errs() << "INC INST NOT BINARY OP" << "\n";
					}
					
					Instruction* inductionVarExitCondCopy = inductionVarExitCond->clone();	//To put at entry: BB checking before starting loop
					inductionVarExitCondCopy->setOperand(0, loadedIterVarStart);
					inductionVarExitCondCopy->setOperand(1, loadedIterVarEnd);
					inductionVarExitCondCopy->insertBefore(&(BB2.back()));
					BranchInst* last = dyn_cast<BranchInst>(&(BB2.back()));
					BasicBlock* ifTrue = last->getSuccessor(0);
					BranchInst::Create(ifTrue, &(newFn->back()), inductionVarExitCondCopy, last);
					last->eraseFromParent();
				
				}
				else {	// DOALL, change iteration end value
					inductionVarExitCond->setOperand(1, loadedIterVarEnd);
				
				}
				
				phi->setIncomingValue(preHeader, loadedIterVarStart);
				
				for(auto* I: iterationVarUsed) {
					I->replaceUsesOfWith(iterationVar, gepInstIter);
				}
				
				
				// Now all we have left is creating the required struct in oldFn and calling pthread_create and pthread_join
				Instruction& toAddBefore = entryBB.back();
				
				// Allocate and store values in innerSt
				AllocaInst* innerStOldFn = this->populateInnerStInOldFunction(BB2, innerStTy, toAddBefore);
				
				// To get pointer of innerSt, allocate memory for innerSt* and store innerSt into this
				AllocaInst* innerStPtrOldFn = new AllocaInst(PointerType::get(innerStTy, 0), "innerStPtrOldFn", &toAddBefore);
				new StoreInst(innerStOldFn, innerStPtrOldFn, &toAddBefore);
				LoadInst* loadedInnerStPtrOldFn = new LoadInst(innerStPtrOldFn, "innerStPtrOldFn", &toAddBefore);	// For use in OuterSt
				
				if (DEBUGG) {
					errs() << F << "\n";
					errs();
					errs() << *newFn << "\n";
				}
				
				
				// Now create outer St in OldFn, this has to be done in a loop depending on core_count
				IRBuilder<> builder(&toAddBefore);
				std::vector<std::vector<Value*>> PTC_Call_Args;
				std::vector<std::vector<Value*>> PTJ_Call_Args;
				std::vector<AllocaInst*> PTJ_Threadnum_Args;
				Function* pthread_create = M.getFunction("pthread_create");
				Function* pthreadJoin = M.getFunction("pthread_join");
				
				if (LoadInst* loadedIteration = dyn_cast<LoadInst>(iterationEndValue)) {
					// If iterationEndValue is a LoadInst then it resides inside the loop (which is in newFn) so need a local Load in OldFn
					iterationEndValue = builder.CreateLoad(loadedIteration->getOperand(0), "loadIterationEndValue");
					loadedIteration->eraseFromParent();
				}
				
				std::vector<AllocaInst*> locks;
				std::vector<AllocaInst*> kills;
				if (DOACROSS) {
					// Allocate core_count number of AllocaInst to store n many lock locations
					for (unsigned int i=0; i<startValues.size(); i++) {
						AllocaInst* allocated = new AllocaInst(Type::getInt32Ty(M.getContext()), "memLoc", &toAddBefore);
						AllocaInst* kill = new AllocaInst(Type::getInt32Ty(M.getContext()), "killSignal", &toAddBefore);
						Value* semValue = ConstantInt::getSigned(Type::getInt32Ty(F.getContext()), 0);
						new StoreInst(semValue, allocated, &toAddBefore);
						new StoreInst(semValue, kill, &toAddBefore);
						locks.push_back(allocated);
						kills.push_back(kill);
					}
				}
				
				for (unsigned int i=0; i<startValues.size(); i++) {
					AllocaInst* outerStOldFn;
					Value* iterEnd;
					if (DOACROSS) {
						// Store the two ThreadLock values into outerSt
						AllocaInst* waitLoc = locks[i];
						AllocaInst* signalLoc = locks[(i + 1) % thread_count];
						AllocaInst* currThreadKill = kills[i];
						AllocaInst* nextThreadKill = kills[(i + 1) % thread_count];
						ConstantInt* iterStartConst = startValues[i];
					
						iterEnd = iterationEndValue;	// Changes for DOALL
						if (DEBUGG) {errs() << "IterEnd: " << *iterEnd << "\n";}
						outerStOldFn = this->populateOuterStInOldFunction(outerStTy, waitLoc, signalLoc, currThreadKill, nextThreadKill, iterStartConst, iterEnd, loadedInnerStPtrOldFn, BB2, toAddBefore);
					
					}
					
					else {	//DOALL 
						
						Value* iterStartNew = startValues[i];
						iterEnd = endValues[i];
						
						outerStOldFn = this->populateOuterStInOldFunction(outerStTy, iterStartNew, iterEnd, loadedInnerStPtrOldFn, BB2, toAddBefore);
						
					}					
					
				
					std::vector<Value*> PTC_args;
					AllocaInst* threadNum = new AllocaInst(Type::getInt64Ty(M.getContext()), "threadNum", &toAddBefore);
					PTC_args.push_back(threadNum);
				
					PointerType* nn = PointerType::get(this->unionattr, 0);
					ConstantPointerNull* nnn = ConstantPointerNull::get(nn);
					PTC_args.push_back(nnn);
				
					PTC_args.push_back(newFn);
					
					// Create function Arg for pthread_create
					BitCastInst* newFNARG = new BitCastInst(outerStOldFn, Type::getInt8PtrTy(M.getContext()), "NewFnArgCast", &toAddBefore);
					PTC_args.push_back(newFNARG);
				
					// Even though create can be added here, testing showed it is better if we put all create together at last 
					// builder.CreateCall(pthread_create, PTC_args);
					PTC_Call_Args.push_back(PTC_args);
					PTJ_Threadnum_Args.push_back(threadNum);
				
				}
				
				for (auto args:PTC_Call_Args) {
					builder.CreateCall(pthread_create, args); 
					// We don't put a pthread_join call here otherwise we wait till thread finished until we call next pthread_create, essestially doing it sequentially!
				}
				
				if (DOACROSS) {
					//Signal the first thread to start work
					this->insertSignal(locks[0], &toAddBefore, &F);
				}
				
				for (auto threadNum: PTJ_Threadnum_Args) {
					std::vector<Value*> PTJ_args;
				
					LoadInst* loadedThreadnum = new LoadInst(threadNum, "loadedThreadnum", &toAddBefore);
					PTJ_args.push_back(loadedThreadnum);
									
					PointerType* ppnull = PointerType::get(PointerType::get(Type::getInt8Ty(M.getContext()), 0), 0);
					ConstantPointerNull* pppnull = ConstantPointerNull::get(ppnull);
					PTJ_args.push_back(pppnull);
					
					builder.CreateCall(pthreadJoin, PTJ_args);
				}
				
			}
			
			return true;
		}
	};
}


char parallelise::ID = 0;
static RegisterPass<parallelise> X("paralleliseLoops", "Run parallelisation loop transformation", false, false);
