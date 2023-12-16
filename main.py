import sys
import sexp
import pprint
import translator
from z3 import *

def Extend(Stmts,Productions):
    ret = []
    for i in range(len(Stmts)):
        prefix = Stmts[0:i]
        suffix = Stmts[i+1:]
        if type(Stmts[i]) == list:
            TryExtend = Extend(Stmts[i],Productions)
            if len(TryExtend) > 0 :
                for extended in TryExtend:
                    ret.append(prefix+[extended]+suffix)
                break
        elif type(Stmts[i]) == tuple:
            continue
        elif Stmts[i] in Productions:
            for extended in Productions[Stmts[i]]:
                ret.append(prefix+[extended]+suffix)
            break
    return ret

def stripComments(bmFile):
    noComments = '(\n'
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + '\n)'


if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0] #Parse string to python list
    checker=translator.ReadQuery(bmExpr)
    SynFunExpr = []
    StartSym = 'My-Start-Symbol' #virtual starting symbol
    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
    FuncDefine = ['define-fun']+SynFunExpr[1:4] #copy function signature
    #print(FuncDefine)
    BfsQueue = [[StartSym]] #Top-down
    Productions = {StartSym:[]}
    Type = {StartSym:SynFunExpr[3]} # set starting symbol's return type
    for NonTerm in SynFunExpr[4]: #SynFunExpr[4] is the production rules
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        if NTType == Type[StartSym]:
            Productions[StartSym].append(NTName)
        Type[NTName] = NTType
        Productions[NTName] = NonTerm[2]
    Count = 0
    Flag = 0
    TE_set = set()
    while(len(BfsQueue)!=0):
        Curr = BfsQueue.pop(0)
        TryExtend = Extend(Curr,Productions)
        if(len(TryExtend)==0): # Nothing to
            FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True) # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.
            
            # 调用z3前检查生成函数是否包含所有形参使用，目前有bug，无法处理实参形参名字不同的情况，如tutorial.sl
            TestFlag_checkAllValUsed = False
            if TestFlag_checkAllValUsed:
                tmp_set = set()
                def AllValUsed(root):
                    for i in root:
                        if isinstance(i, str):
                            tmp_set.add(i)
                        elif isinstance(i, (list, tuple)):
                            AllValUsed(i)
                AllValUsed(Curr)
                tmp_Flag = 1
                for i in checker.VarTable.items():
                    if not i in tmp_set:
                        tmp_Flag = 0
                        break
                if not tmp_Flag:
                    continue
                
            CurrStr = translator.toString(Curr)
            Str = FuncDefineStr[:-1]+' '+ CurrStr+FuncDefineStr[-1] # insert Program just before the last bracket ')'
            Count += 1
            # print (Count)
            # print (Str)
            
            # 存储现有反例，优先验证已存储的反例是否满足
            # new_checker只返回是否满足，失败不返回model
            if Flag == 1:
                if checker.new_check(Str):
                    continue
                else:
                    checker.solver.pop()
                    Flag = 0                    
            counterexample = checker.check(Str)
            if(counterexample == None): # No counter-example
                Ans = Str
                break
            else:
                checker.solver.push()
                for value in checker.VarTable.values():
                    if counterexample[value] == None:
                        checker.solver.add(value == 0)
                    else:
                        checker.solver.add(value == counterexample[value])
                Flag = 1
            
        for TE in TryExtend:
            TE_str = str(TE)
            if not TE_str in TE_set:
                BfsQueue.append(TE)
                TE_set.add(TE_str)

    print(Ans)
    with open('result.txt', 'w') as f:
        f.write(Ans)

	# Examples of counter-examples    
	# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int 0)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int x)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (+ x y))'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y x))'))
