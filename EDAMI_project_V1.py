"""------------------------------------------------------------------------------------------
EDAMI Project
TANE Algorithm for discovery of functional dependencies
Prepared by Gabriela Domaradzka and Filip Wasilewski
----------------------------------------------------------------------------------------------"""
# Library loading
from pandas import *
from collections import defaultdict
import numpy as NP
import sys

# Function computing rhs+ candidates C+(X) as an intersection of smaller C+ sets
def findCp(x): 
	global dictCp
	tempItemSet=[]
	for a in x:
		if x.replace(a,'') in dictCp.keys():
			temp = dictCp[x.replace(a,'')]
		else:
			temp=findCp(x.replace(a,'')) #Computing C+(X\{A}) for each A at a time
		tempItemSet.insert(0, set(temp))
	if list(set.intersection(*tempItemSet)) == []:
		Cp = []
	else:
		Cp = list(set.intersection(*tempItemSet))  #Computing the intersection
	return Cp

# Function computing rhs+ candidates C+(X)
# First definition in chapter 3.2.2
def computeCp(x): 
	global colList
	temp_colList = colList[:]
	if x=='': return temp_colList
	Cp = []
	for a in temp_colList:
		for b in x:
			temp = x.replace(a,'')
			temp = temp.replace(b,'')
			if not validfd(temp, b):
				Cp.append(a)
	return Cp

# Function computing dependencies (finds the minimal dependencies with the left-hand side of L(l-1))
# Pseudocode in 4.3. 
def compute_dependencies(level, temp_colList):
    global dictCp
    global FinalFDs
    global colList
    for x in level:
    	tempItemSet=[]
    	for a in x:
    		if x.replace(a,'') in dictCp.keys():
    			temp = dictCp[x.replace(a,'')]
    		else:
    			temp=computeCp(x.replace(a,'')) #Computing C+(X\{A}) for each A at a time
    			dictCp[x.replace(a,'')] = temp
    		tempItemSet.insert(0, set(temp))
    	if list(set.intersection(*tempItemSet)) == []:
    		dictCp[x] = []
    	else:
    		dictCp[x] = list(set.intersection(*tempItemSet))  #Computing the intersection
    for x in level:
    	for a in x:
    		if a in dictCp[x]:
	    		if validfd(x.replace(a,''), a): #Validity testing: check if X\{A}->A is valid
    				FinalFDs.append([x.replace(a,''), a]) #Adding to the final list of dependencies
    				dictCp[x].remove(a)  #Removing A from the rhs+ candidates C+(X)

    				temp_colList=colList[:] 
            #Computing R\X and removing all B in R\X from C+(X)
    				for j in x: #Computing R\X
    					if j in temp_colList: temp_colList.remove(j)

    				for b in temp_colList: #Removing each B 
    					if b in dictCp[x]: dictCp[x].remove(b)

# Function checking if functional dependency is valid using procedure with error e
def validfd(y,z):
	if y=='' or z=='': return False
	ey = computeE(y)
	eyz = computeE(y+z)
	if ey == eyz :
		return True
	else:
		return False

# Function computing error e 
# Measure e is a fraction of tuples with exceptions or errors affecting the dependency
def computeE(x):
	global totaltuples
	global dataPartitions
	doublenorm = 0
	for i in dataPartitions[''.join(sorted(x))]:
		doublenorm = doublenorm + len(i)
	e = (doublenorm-len(dataPartitions[''.join(sorted(x))]))/float(totaltuples)
	return e

# Function checking if X is a superkey
# An attribute set X is a superkey if no two tuples agree on X (partition consists of singleton equivalence classes only)
# The set X is a key if it is a superkey and no proper subset of it is a superkey
def check_superkey(x):
    global dataPartitions
    if ((dataPartitions[x] == [[]]) or (dataPartitions[x] == [])):
        return True
    else:
        return False

# Function with prunning procedure
# Pseudocode in the chapter 4.4.
def prune(level):
    global dictCp
    global FinalFDs
    stufftobedeletedfromlevel = []
    for x in level: 
    	if dictCp[x]==[]: 
    		level.remove(x) #X is deleted if C+(X) is empty
    	if check_superkey(x): #Check if X is a superkey
    		temp = dictCp[x][:]
    		for i in x: #Computing C+(X)\X
    			if i in temp: temp.remove(i)
    		for a in temp: #For each A in C+(X)\X
    			tempItemSet=[]
    			for b in x:
    				if not( ''.join(sorted((x+a).replace(b,''))) in dictCp.keys()): 
    					dictCp[''.join(sorted((x+a).replace(b,'')))] = findCp(''.join(sorted((x+a).replace(b,''))))
    				tempItemSet.insert(0,set(dictCp[''.join(sorted((x+a).replace(b,'')))]))
    			if a in list(set.intersection(*tempItemSet)): 
    				FinalFDs.append([x, a]) #Adding to the final list of functional dependencies
    		if x in level: stufftobedeletedfromlevel.append(x) #Delete X from the level
    for item in stufftobedeletedfromlevel:
    	level.remove(item)

# Function generating levels
# A level is the collection of attribute sets, the sets can potentially be used to construct dependencies    	
# Pseudocode in the chapter 4.2.
# The procedure generates level L_l+1 from the level L_l
def generate_next_level(level):
    nextlevel=[]
    for i in range(0,len(level)): #Choosing an element
        for j in range(i+1, len(level)): #Comparing with the next elements 
            if ((not level[i]==level[j]) and level[i][0:-1]==level[j][0:-1]): 
                x = level[i]+level[j][-1]       
                flag = True
                for a in x: 
                    if not(x.replace(a, '') in level):
                        flag=False
                if flag==True:
                    nextlevel.append(x)
                    stripped_product(x, level[i] , level[j] ) 
    return nextlevel

# Function computing partitions
# Pseudocode in the chapter 4.5.
def stripped_product(x,y,z):
	global dataPartitions
	global tableT
	tableS = ['']*len(tableT)
	partitionY = dataPartitions[''.join(sorted(y))] 
	partitionZ = dataPartitions[''.join(sorted(z))]
	partitionofx = [] 
	for i in range(len(partitionY)): 
		for t in partitionY[i]: 
			tableT[t] = i
		tableS[i]='' 
	for i in range(len(partitionZ)): 
		for t in partitionZ[i]: 
			if ( not (tableT[t] == 'NULL')):
				tableS[tableT[t]] = sorted(list(set(tableS[tableT[t]]) | set([t]))) 
		for t in partitionZ[i]: 
			if (not (tableT[t] == 'NULL')) and len(tableS[tableT[t]])>= 2 : 
				partitionofx.append(tableS[tableT[t]]) 
			if not (tableT[t] == 'NULL'): tableS[tableT[t]]='' 
	for i in range(len(partitionY)): 
		for t in partitionY[i]: 
			tableT[t]='NULL'
	dataPartitions[''.join(sorted(x))] = partitionofx

# Function computing singleton partitions (equivalence classes of size 1 are removed)
def computeSingletonPartitions(temp_colList):
	global data2D
	global dataPartitions	
	for a in temp_colList:
		dataPartitions[a]=[]
		for element in list_duplicates(data2D[a].tolist()):
			if len(element[1])>1: 
				dataPartitions[a].append(element[1])

# Returns the equivalence classes with all their appearances
def list_duplicates(seq):
    tally = defaultdict(list)
    for i,item in enumerate(seq):
        tally[item].append(i)
    return ((key,locs) for key,locs in tally.items() 
                            if len(locs)>0)

def FDSortIndex(item):
	return item[0] + item[1]

"""------------------------------------------------------------------------------------------
Application of the TANE algorithm
----------------------------------------------------------------------------------------------"""

data2D = read_csv(str(sys.argv[1])) #Upload data in .csv format

totaltuples = len(data2D.index)
colList = list(data2D.columns.values)
tableT = ['NULL']*totaltuples #tableT is used in the the function stripped_product

L0 = []
dictCp = {'NULL': colList}
dataPartitions = {} 
computeSingletonPartitions(colList)
FinalFDs=[]
L1=colList[:] 
l=1
L = [L0,L1]

while (not (L[l] == [])):
    compute_dependencies(L[l],colList[:])
    prune(L[l])
    temp = generate_next_level(L[l])
    L.append(temp)
    l=l+1


f = open("tane_results.txt", "w")
message = str()


print ("\nFound total number of ", len(FinalFDs), " FDs for the dataset ", str(sys.argv[1]), ".")
f.write(("Found total number of "+ str(len(FinalFDs))+ " FDs for the dataset "+ str(sys.argv[1])+ ".\n"))
print("\nList of all FDs:\n")
FinalFDs.sort(key = FDSortIndex)
for fd in FinalFDs:
	print(fd[0] + ' --> ' + fd[1])
	f.write(fd[0] + ' --> ' + fd[1] +"\n")

f.close()