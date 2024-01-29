from array import *
from calendar import c
import string
import sys
import signal
from time import process_time
import random
from priority_queue import PriorityQueue
from timeit import default_timer as timer

start = timer()

def sigint_handler(signum, frame):
    print("c Cancelled")
    print("s UNKNOWN")
    print("c Percentage of reused:"+ str(round(s.numberreused/(s.numberreused+s.numbernonreused)*100 , 2) if s.numberreused+s.numbernonreused>0 else 0 ))
    print("c Total num MaxRes:"+str(s.numres))	
    print("c Total num MaxRes attepmt:"+str(s.numresAttempt))
    print("c Ratio of soft clause successful MaxRes:" + str(round(s.soft_succ/s.soft_total)))
    sys.exit(0)

signal.signal(signal.SIGINT, sigint_handler)

class MaxSATSolver: #once bu bos listeler olusturuluyor
    def __init__(self):
        self.nvar=0
        self.clauses = [] 
        self.nclauses =0
        self.noccurs = [] 
        self.Noccurlit=[]
        self.occurlist =[]
        #self.removed = []
        self.neighbours = []
        self.emptyclauses = 0
        self.model = []
        self.varremoved=[]
        self.weight=[]
        self.hardweight=9223372036854775807 #INT64_MAX, no instance of the evaluation exceeds this value
        self.sortbyweight=0
        self.abst=[]
        self.reuseEnabled=True
        self.heur=0
        self.numbernonreused=0
        self.numberreused=0
        self.numres=0
        self.numresAttempt=0
        self.seen = []
        self.maxRemoveSize=-1
        self.maxRemoveTime=300
        self.soft_total=0
        self.soft_succ=0
        


    def parsedimacs(self , fileName):

        file1 = open(fileName, 'r')
        line = file1.readline()
        while line:

            arr = array('i', [])
            i=0
           
            if not line in ['\n', '\r\n'] and line[0]!="c" :
                if line[0]=="p":
                    self.hardweight = int(line.split()[4]) #getting the top weight in the input file
                else:
                    for var in line.split():
                        if var=="h":
                            w=self.hardweight
                        else:
                            var=int(var)
                            if i== 0:
                                w=var
                            elif var != 0 :
                                arr.append((-var-1)*2+1 if var < 0 else (var-1)*2 )
                                if abs(var) > self.nvar:
                                    self.nvar= abs(var)
                        i+=1
                    arr=sorted(arr)
                    if not self.isTautology(arr):
                       if self.addclauseWithoutRepeat(arr,w) :
                           self.updateoccurlist(arr)
            line = file1.readline()
            
        
        file1.close()
        #print(nvar)
#burda daha sonra kullanmalik var tanimlaniyor
        #counting number of clauses in which each variable occurs
        self.numbernonreused=0
        self.numberreused=0 #now we are starting the count how many times we are increasing the weight
        self.noccurs = [0] * self.nvar #counting variable
        self.Noccurlit = [0] *self.nvar*2 #counting literals , every variable has two literals 
        self.neighbours = [0]*self.nvar
        self.seen = [False] * self.nvar
        self.model = [False]*self.nvar
        self.varremoved=[False]*self.nvar
        for clause_id in range(len(self.clauses)):
            clause = self.clauses[clause_id]
            for lit in clause:
                var = lit//2
                self.noccurs[var]+=1
                self.Noccurlit[lit]+=1
            #print(noccurs)
            #print(Noccurlit)
            #print(occurlist)

        self.countNeighboursOfList(range(0,self.nvar))
        if self.heur==0:
            self.orderHeap = PriorityQueue([(self.neighbours[var],var) for var in range(0,self.nvar)])
       

    def isTautology(self, clause):
        for i in range(len(clause)-1):
            if clause[i]//2 == clause[i+1]//2:
                return True
        return False
    
    def isHardclause(self , clause_id):
        return self.weight[clause_id]>=self.hardweight

    def countNeighboursOfList(self, list):
        for var in list:
            self.countNeighbours(var)

    def countNeighbours(self, var):
        poslit = var*2
        neglit = var*2+1
        self.seen[var] = True
        seenlist= [var]
        for clause_id in self.occurlist[poslit]:
            if not self.removed(clause_id):
                cl=self.clauses[clause_id]
                for lit in cl:
                    var2 = lit //2
                    if not self.seen[var2]:
                        seenlist.append(var2)
                        self.seen[var2]=True
        for clause_id in self.occurlist[neglit]:
            if not self.removed(clause_id):
                cl=self.clauses[clause_id]
                for lit in cl:
                    var2 = lit //2
                    if not self.seen[var2]:
                        seenlist.append(var2)
                        self.seen[var2]=True    
        self.neighbours[var] = len(seenlist)-1
        for var2 in seenlist:
            self.seen[var2] = False


    def getNeighbours(self, var):
        neigh=[]
        poslit = var*2
        neglit = var*2+1
        self.seen[var] = True
        for clause_id in self.occurlist[poslit]:
            if not self.removed(clause_id):
                cl=self.clauses[clause_id]
                for lit in cl:
                    var2 = lit //2
                    if not self.seen[var2]:
                        neigh.append(var2)
                        self.seen[var2]=True
        for clause_id in self.occurlist[neglit]:
            if not self.removed(clause_id):
                cl=self.clauses[clause_id]
                for lit in cl:
                    var2 = lit //2
                    if not self.seen[var2]:
                        neigh.append(var2)
                        self.seen[var2]=True    
        for var2 in neigh:
            self.seen[var2] = False
        self.seen[var]=False
        return neigh
    
    
    def MaxRes(self , clause1 , clause2 , resvar , res0 , respos, resneg):
        self.numresAttempt+=1
        i = 0
        j = 0    
        w=min(clause1[1] , clause2[1])
        while i < len(clause1[0]) and j < len(clause2[0]):
            var1 = clause1[0][i]//2
            var2 = clause2[0][j]//2
            if var1 == var2 :
                if clause1[0][i] == clause2[0][j]:
                    res0[0].append(clause1[0][i])
                    i+=1
                    j+=1
                elif var1 == resvar : 
                    i+=1
                    j+=1
                else :
                    return False  # this returns true if the first position of the max res returns tautl
            else :
                if clause1[0][i]> clause2[0][j]:
                    res0[0].append(clause2[0][j])
                    j+=1
                else:
                    res0[0].append(clause1[0][i])
                    i+=1
        while i < len(clause1[0]): 
            res0[0].append(clause1[0][i])
            i+=1
        while j < len(clause2[0]):
            res0[0].append(clause2[0][j])
            j+=1
        res0[1]=w
    #implemention of compansation clauses
        if clause1[1] <self.hardweight:
            for l in range(1 , len(clause2[0])+1):
                if clause2[0][l-1] // 2 != resvar :
                    res=[]
                    if self.mergeMaxRes(clause1[0] , clause2[0] , l , resvar ,res):
                        respos.append([res , w])
                        self.soft_succ=+1 #if you come from here with soft clause that means this clause is successfully applied maxres
                    #print(l)
                    #print(clauses)
            self.soft_total=+1 #count if clause the clause that we are dealing with is soft
        if clause2[1]< self.hardweight:
            for l in range(1 , len(clause1[0])+1):
                if clause1[0][l-1] // 2 != resvar :
                    res=[]
                    if self.mergeMaxRes(clause2[0] , clause1[0] , l , resvar,res):
                        resneg.append([res , w])
                        self.soft_succ=+1 #count the successfull maxres in soft clause
                    #print(l)
                    #print(clauses)
            self.soft_total=+1 #count if clause the clause that we are dealing with is soft
        self.numres+=1
        return True
  

    def neg(self, lit):
        if lit %2 == 0:
            return lit+1
        else:
            return lit-1
        
        
    def mergeMaxRes(self , fullclause , parclause , l , resvar, res):
        i = 0
        j= 0
        while i < len(fullclause) and j < l:
            var1 = fullclause[i]//2
            var2 = parclause[j]//2
            lit1=fullclause[i]
            lit2=parclause[j] if j < l-1 else self.neg(parclause[j])
            if var1 == var2 :
                if lit1 == lit2:
                    res.append(lit1)
                    i+=1
                    j+=1
                elif var1 == resvar : 
                    res.append(lit1)
                    i+=1
                    j+=1
                else :
                    return False
            else :
                if lit1> lit2:
                    res.append(lit2)
                    j+=1
                else:
                    res.append(lit1)
                    i+=1
        while i < len(fullclause): 
            res.append(fullclause[i])
            i+=1
        while j < l:
            res.append(parclause[j] if j < l-1 else self.neg(parclause[j]))
            j+=1
        return True
    
    def printnonremovedclauses(self):
        for i in range(len(self.clauses)):
            if not self.removed(i):
                print(self.clauses [ i] , sep=" ")
    

    def solve(self):
        Usedorder = []
        staticOrder =[]
        random.seed(10000)
        if self.heur ==3: #Lexicographic condition
            staticOrder=range(self.nvar)
        elif self.heur==2: #random condition
            staticOrder=list(range(self.nvar))
            random.shuffle(staticOrder)
        elif self.heur ==1: #static neighbour order condition
            staticOrder=sorted(range(self.nvar) , key=self.orderbyneighbours)

        print("c initial nclauses=" + str(self.nclauses)+" initial nvar="+ str(self.nvar))
        prevmaxRes=0
        prevmaxResAttempt=0
        prevreused=0
        prevnonReused=0
        neigh=[]
        for i in range(self.nvar) :
            if self.heur >=1:
                var=staticOrder[i]
            else:
                (neighSize,var)=self.orderHeap.pop()
            if self.heur==0 and self.maxRemoveSize >= 0 and (neighSize > self.maxRemoveSize or timer()-start > self.maxRemoveTime):
                self.printInstance()
                sys.exit(0)
            neigh=self.getNeighbours(var)
            startRemove=timer()
            self.eliminate(var)
            endRemove=timer()
            self.countNeighboursOfList(neigh)
            if self.heur==0:
                for var2 in neigh:
                    self.orderHeap.update_elem(var2,(self.neighbours[var2],var2))

            nonreused=s.numbernonreused-prevnonReused
            reused=s.numberreused-prevreused
            print("c Removed " + str(var)+ ", "  + str(i+1)+ "/" + str(self.nvar) + ":nclauses=" + str(len(self.clauses)) 
                  +";real_nclauses=" + str(self.nclauses)
                  + ";time_remove="+ str(round(endRemove-startRemove,3))
                  + ";acum_time="+str(round(endRemove-start,3))
                  + ";neigh_size="+str(len(neigh))
                  #+ ";max_neighbour="+str(minmax[0])
                  #+ ";min_neighbour="+str(minmax[1])
                  + ";nmaxRes=" +str(self.numres-prevmaxRes)
                  + ";nmaxResAttempt=" +str(self.numresAttempt-prevmaxResAttempt)
                  + ";percantage_reused="+ str(round(reused/(reused+nonreused)*100 , 2)if reused+nonreused>0 else 0))
           
            prevnonReused=self.numbernonreused
            prevreused=self.numberreused
            prevmaxRes=self.numres    
            prevmaxResAttempt=self.numresAttempt
            #print(self.neighbours)
            #self.printnonremovedclauses()
            Usedorder.append(var)
        for var in reversed(Usedorder):
            poslit = var*2
            neglit = var*2+1
            if len(self.occurlist[poslit]) == 0 :
                self.model[var]= False #assing the 0 
            elif len(self.occurlist[neglit]) == 0 :
                self.model[var]= True #assign the 1 
            else:
                self.model[var]= False #assing 0
                for clause_id in self.occurlist[poslit]:
                    cl=self.clauses[clause_id]
                    if self.implied(cl , var):
                        self.model[var]= True #assign the 1
                        break

            if  self.model[var]:
                for clause_id in self.occurlist[neglit]:
                        cl=self.clauses[clause_id]
                        if not self.satisfied(cl):
                            print("ERROR at var " + str(var) + " clause ", sep="")
                            print(cl)
                            break
            else:
                for clause_id in self.occurlist[poslit]:
                        cl=self.clauses[clause_id]
                        if not self.satisfied(cl):
                            print("ERROR at var " + str(var) + " clause ", sep="")
                            print(cl)
                            break

    
    def implied(self , cl , var) :
        for lit in cl:
            if var != lit//2 and self.value(lit):
                return False
            
        return True
    
    def satisfied(self , cl) :
        for lit in cl:
            if self.value(lit):
                return True
        
        return False

    def isposlit(self, lit):
        return lit %2 == 0

    def value(self , lit):
        if self.isposlit(lit):
            return self.model[lit //2]
        else:
            return not self.model[lit //2]

    def orderbyoccurlist(self , var):
        return self.noccurs[var]
    
    def orderbyneighbours(self , var):
        return self.neighbours[var] if not self.varremoved[var] else self.nvar
    
    def orderbyweight(self , clause_id):
        return self.weight[clause_id]
    
    def removed (self , clause_id):
        return self.weight[clause_id]==0  #checks if the clause is removed , the removed conditions is weight 0

    def eliminate(self , var):
        poslit = var*2
        neglit = var*2+1
        self.cleanlist(self.occurlist[poslit],False)
        self.cleanlist(self.occurlist[neglit],False) #cleaning step already clauses
        if self.sortbyweight==1: 
            self.occurlist[poslit]=sorted(self.occurlist[poslit] , key=self.orderbyweight) 
            self.occurlist[neglit]=sorted(self.occurlist[neglit] , key=self.orderbyweight) #after cleaning the occurlists , order by weight
        elif self.sortbyweight==2:
            self.occurlist[poslit]=sorted(self.occurlist[poslit] , key=self.orderbyweight, reverse=True)
            self.occurlist[neglit]=sorted(self.occurlist[neglit] , key=self.orderbyweight, reverse=True) #after cleaning the occurlists , order by weight
#neglit =self.neg(poslit)
            
        i = 0
        while i <len(self.occurlist[poslit]):
            j=0
            clausei_id = self.occurlist[poslit][i] 
            if not self.removed (clausei_id) :
                clausei = self.clauses[clausei_id]
                while j < len(self.occurlist[neglit]):
                    clausej_id = self.occurlist[neglit][j]
                    if not self.removed (clausej_id) : 
                        clausej = self.clauses[clausej_id]
                        res0 = [[],0]
                        respos = []
                        resneg = []
                        if self.MaxRes([clausei,self.weight[clausei_id]] , [clausej , self.weight[clausej_id]] , var , res0 ,respos , resneg ) :
                            #print("clause one = " + str(clausei))
                            #print("clause two = " + str(clausej))
                            #print("result is  " + str(res0))
                            w=min(self.weight[clausei_id] , self.weight[clausej_id])
                            if len(res0[0])==0:
                                self.emptyclauses+=res0[1]
                            else:
                                if self.addclauseWithoutRepeat(res0[0],res0[1]):
                                    self.updateoccurlist(res0[0])
                            for cl in respos :
                                if self.addclauseWithoutRepeat(cl[0] , cl[1]):
                                    self.occurlist[poslit].append(len(self.clauses)-1)

                            for cl in resneg:
                                if self.addclauseWithoutRepeat(cl[0] , cl[1]):
                                    self.occurlist[neglit].append(len(self.clauses)-1)
                            if not self.isHardclause(clausej_id):
                                self.weight[clausej_id]-=w
                                if self.weight[clausej_id]==0:
                                    self.nclauses-=1
                            if not self.isHardclause(clausei_id):
                                self.weight[clausei_id]-=w
                                if self.weight[clausei_id]==0:
                                    self.nclauses-=1
                            if self.weight[clausei_id]==0:
                                break
                    j+=1
            i+=1
        self.cleanlist (self.occurlist[neglit],True)
        self.cleanlist (self.occurlist[poslit],True) #to get Di
        self.varremoved[var]=True
 

    def addclause(self , cl,w,a):
        self.clauses.append(cl)
        #self.removed.append(False)
        self.weight.append(w)
        self.abst.append(a)
        self.nclauses+=1


    def updateoccurlist(self , cl):
        for lit in cl :
            self.occurlist[lit].append(len(self.clauses)-1)

        
    def addclauseWithoutRepeat (self,cl ,w):
        smalit=-1 #literal with smallest occurlist
        length=len(self.clauses)+1 #upperbound of the size of an occurlist
        a=0
        for lit in cl :
            var=lit//2
            litneg=var*2+1
            a = a | 1<<(lit%64) #2^lit%64 
            if len(self.occurlist)<litneg+1:
                for i in range(len(self.occurlist) , litneg+1):#occurlist i var geldikce olusturuyorduk, simdi butun var icin ikis lit olusturuldu
                    self.occurlist.append([])
            if len(self.occurlist[lit]) < length: #checking the literal if it has the smallest occurlist
                smalit=lit
                length=len(self.occurlist[lit])
        reused=False
        if self.reuseEnabled: 
            for clause_id in self.occurlist[smalit]:
                if self.weight[clause_id]>0 and self.abst[clause_id]==a: #checking the weight and abst
                    if cl == self.clauses[clause_id]:
                        if self.isHardclause(clause_id) or w>=self.hardweight:
                            self.weight[clause_id]=self.hardweight
                        else:
                            self.weight[clause_id]+=w
                        reused=True
                        break
        if not reused :
            self.addclause(cl,w,a)
            self.numbernonreused+=1
        else:
            self.numberreused+=1
        return not reused #if its false increased a weight

    def printInstance(self):
        for cl_id in range(len(self.clauses)):
            if not self.removed(cl_id):
                cl = self.clauses[cl_id]
                if self.isHardclause(cl_id):
                    print("h",end="")
                else:
                    print(self.weight[cl_id],end="")
                for lit in cl:
                    if self.isposlit(lit):
                        print(" " + str(lit//2+1), end="")
                    else:
                        print(" -" + str(lit//2+1), end="")
                print(" 0")
    
    def cleanlist (self , list, remove):
        j = 0 
        j2 = 0
        while j < len(list):
            clausej_id = list[j]
            if not self.removed (clausej_id) :
                list[j2] = clausej_id
                j2+=1
                if remove :
                    self.weight [clausej_id] = 0
                    self.nclauses-=1
            j+=1
        del list[j2:j]

    def parsesolution(self,fileName):
        file1 = open(fileName, 'r')
        value=-1
        first=file1.read(1)
        while first:
            if first=="c" or first=="s":
                file1.readline()
            elif first=="o":
                file1.read(1)
                value=int(file1.readline())
            elif first=="v":
                file1.read(1)
                for v in range(self.nvar):
                    val = file1.read(1)
                    self.model[v]= int(val)==1
                file1.readline()
            else:
                file1.readline()
            first=file1.read(1)
        return value

    def checksolution(self,value):
        count=0
        for clause_id in range(len(self.clauses)):
            cl = self.clauses[clause_id]
            if self.isHardclause(clause_id) and not self.satisfied(cl):
                print("Hard clause " + str(clause_id) + " not satisfied")
            elif not self.isHardclause(clause_id) and  not self.satisfied(cl):
                count+=self.weight[clause_id]
        if not value==count :
            print("Wrong cost: expected " + str(count) + " found " + str(value))


   
s=MaxSATSolver()

i=1
while sys.argv[i][0]== "-":
    if sys.argv[i] == "-sort":#sort occurlist when removing var
            s.sortbyweight=int(sys.argv[i+1])
            i+=1
    elif sys.argv[i]== "-heur":#selecting the different heur.
           s.heur= int(sys.argv[i+1])
           i+=1
    elif sys.argv[i]== "-m":#merge the clauses if they are the same increase the weight
            s.reuseEnabled=int(sys.argv[i+1])!=0
            i+=1
    elif sys.argv[i]== "-v":
            print("c This is Elifnaz Solver weighted version")
            sys.exit(0)
    elif sys.argv[i]=="-r":
            s.maxRemoveSize=int(sys.argv[i+1])
            i+=1
    elif sys.argv[i]== "-h":
            print("c This is Elifnaz Solver weighted version")
            print("c To solve an instance: python3 " + sys.argv[0] + " [options]  instancefile") 
            print("c To check a solution file: python3 " + sys.argv[0] + " instancefile solutionfile")
            sys.exit(0)
    else :
            print("option" + sys.argv[i] + "does not exist" ,file=sys.stderr)
            sys.exit(0)
    i+=1


if i == len(sys.argv)-1 :
    heurnames=["Dynamic Neighbour","Static Neighbour","Random", "Lexicographic"]
    print("c This is Elifnaz Solver weighted version")
    print("c Heuristic="+heurnames[s.heur])
    print("c Reuse Enabled=" + str(s.reuseEnabled))
    print("c Sort Occurlist="+str(s.sortbyweight))
    startParse=timer()
    print("c Starting parse")
    s.parsedimacs(sys.argv[i])
    endParse=timer()
    print("c Parse finished in " + str(round(endParse - startParse,3)))
    print("c Starting solve")
    s.solve()
    print("s OPTIMUM FOUND")
    print("o " + str(s.emptyclauses))
    print("v " , end="")
    for v in range(s.nvar):
        print(1 if s.model[v] else 0 , end="")
    print("")
    end = timer()
    print("c Total time:" + str(round(end - start,3))) 
    print("c Total time without parse:" + str(round(end - endParse,3))) 
    print("c Percentage of reused:"+ str(round(s.numberreused/(s.numberreused+s.numbernonreused)*100 , 2) if s.numberreused+s.numbernonreused>0 else 0 ))
    print("c Total num MaxRes:"+str(s.numres))
    print("c Total num MaxRes attepmt:"+str(s.numresAttempt))
    print("c Ratio of soft clause successful MaxRes:" + str(round(s.soft_succ/s.soft_total)))
else:
    s.reuseEnabled=False
    s.parsedimacs(sys.argv[i])
    value = s.parsesolution(sys.argv[i+1])
    if value!=-1:
        s.checksolution(value)


