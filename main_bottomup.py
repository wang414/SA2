import sys
import sexp
import pprint
import translator
from pdb import set_trace as st
import queue


def Extend(Stmts,Productions):
    ret = []
    for i in range(len(Stmts)):
        if type(Stmts[i]) == list:
            TryExtend = Extend(Stmts[i],Productions)
            if len(TryExtend) > 0 :
                for extended in TryExtend:
                    ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
                break
        elif type(Stmts[i]) == tuple:
            continue
        elif Stmts[i] in Productions:
            for extended in Productions[Stmts[i]]:
                ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
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
    #print(bm)
    #st()
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0] #Parse string to python list
    #pprint.pprint(bmExpr)
    checker=translator.ReadQuery(bmExpr)
    #print (checker.check('(define-fun f ((x Int)) Int (mod (* x 3) 10)  )'))
    #raw_input()
    SynFunExpr = []
    StartSym = 'My-Start-Symbol' #virtual starting symbol
    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
    FuncDefine = ['define-fun']+SynFunExpr[1:4] #copy function signature
    #print("FuncDefine: ",FuncDefine)
    #st()

    BfsPriorityQueue = queue.PriorityQueue()  #Bottom-up
    # BfsQueue = [[StartSym]] #Top-down
    
    len_cnt = {1:1}

    BfsPriorityQueue.put([1, 1, [StartSym]])
    Productions = {StartSym:[]}
    Type = {StartSym:SynFunExpr[3]} # set starting symbol's return type
    #print("Type: ",Type)
    #print(SynFunExpr[4])
    #st()
    for NonTerm in SynFunExpr[4]: #SynFunExpr[4] is the production rules
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        if NTType == Type[StartSym]:
            Productions[StartSym].append(NTName)
        Type[NTName] = NTType
        Productions[NTName] = NonTerm[2]
    #print("type: ",Type)
    # print("pro: ",Productions)
    #st()
    Count = 0
    TE_set = set()
    max_size = 100
    cur_size = 1
    cnt = 0
    while(not BfsPriorityQueue.empty()):
        Curr = BfsPriorityQueue.get()[2]
        # BfsPriorityQueue
        """print("extend", Curr)"""
        TryExtend = Extend(Curr,Productions)
        """print("TryExtend: ",TryExtend)
        st()"""
        if(len(TryExtend)==0): # Nothing to
            #print("funcdefine: ",FuncDefine)
            # print("find", Curr)
            FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True) # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.
            CurrStr = translator.toString(Curr)
            #SynFunResult = FuncDefine+Curr
            #Str = translator.toString(SynFunResult)
            Str = FuncDefineStr[:-1]+' '+ CurrStr+FuncDefineStr[-1] # insert Program just before the last bracket ')'
            # print("str: ",Str)
            Count += 1
            # print (Count)
            # print (Str)
            # if Count % 100 == 1:
                # print (Count)
                # print (Str)
                #raw_input()
            #print '1'
            counterexample = checker.check(Str)
            cnt+=1
            # print(counterexample)
            if(counterexample == None): # No counter-example
                Ans = Str
                break
            #print '2'
        # print("TryExtend")
        # print(TryExtend)
        #raw_input()
        #BfsQueue+=TryExtend
        #TE_set = set()
        for TE in TryExtend:
            TE_str = str(TE)
            # print(f"TE{TE}")
            if not TE_str in TE_set:
                if not len(TE) in len_cnt:
                    len_cnt[len(TE)] = 1
                else:
                    len_cnt[len(TE)] += 1
                BfsPriorityQueue.put([len(TE), len_cnt[len(TE)], TE])
                TE_set.add(TE_str)           
        # exit()   
        """print("TE_set: ",TE_set)
        print("BfsQueue: ",BfsQueue)
        st()"""
    print(cnt)
    print(Ans)
    with open('result.txt', 'w') as f:
        f.write(Ans)

	# Examples of counter-examples    
	# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int 0)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int x)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (+ x y))'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y x))'))
