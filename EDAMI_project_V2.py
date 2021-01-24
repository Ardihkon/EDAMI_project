"""------------------------------------------------------------------------------------------
EDAMI Project
TANE Algorithm for discovery of functional dependencies
Prepared by Gabriela Domaradzka and Filip Wasilewski
----------------------------------------------------------------------------------------------"""
# Library loading
from pandas import *
from collections import defaultdict
import numpy as NP
import itertools
import sys

#print and write to file at the same time
def printAndWrite(text, f):
	print(text)
	f.write(text + "\n")


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
Functions needed to compute minimal cover
------------------------------------------------------------------------------------------"""

def attrclosure(ta, fds, attrs):
	a = {x for x in ta} if type(ta) is not set else ta
	r = a.copy()
	oldr = None
	while oldr != r:
		oldr = r
		for f in fds:
			# if r has all the attributes that the present
			# fd's lhs has, then assert all the rhs values in
			# the value of r.
			if f[0].issubset(r):
				r = r.union(f[1])

	return r.difference(a), fds, attrs

# returns the fd closure for the currently known attributes and
# fds.  the return set is a list of tuples where each element in
# the list is a functional dependency. All FDs are returned in
# non-trivial form; i.e. nothing on the LHS appears on the
# RHS. The tuple consists of three parts, the first is the LHS,
# the second is the RHS, and the third is either a single
# character or the empty string. The first two are python sets,
# and the third indicates whether the LHS is a key (k) or superkey
# (s), or neither (-)
def fdclosure(fds, attrs):
	retval = []
	allkeys, fds, attrs = keys(fds, attrs)

	for l in range(0, len(attrs)):
		for k in itertools.combinations(attrs, l+1):
			r, fds, attrs = attrclosure(k,  fds, attrs)
			if len(r) > 0:
				if k in allkeys:
					iskey = 'k'
				else:
					temp, fds, attrs = attrclosure(k, fds, attrs)
					temp.union(k)

					if temp == attrs:
						iskey = 's'
					else:
						iskey = None

				retval.append((set(k), r, iskey))

	return retval, fds, attrs

# returns the keys of the currently known fds (and
# attributes). Return set is a list of python sets.
def keys(fds, attrs):
	keys = []

	for l in range(0, len(attrs)):
		for c in itertools.combinations(attrs, l+1):

			# if there is a key that is a subset of the candidate, we
			# can skip it, i.e. candidate is a superkey.
			if len([k for k in keys if set(k).intersection(c) ==
					set(k)]) > 0:
				continue

			temp, fds, attrs = attrclosure(c, fds, attrs)
			if temp.union(c) == attrs:
				keys.append(c)

	return keys, fds, attrs

def minimalCover(fds, attrs):
	# the minimal cover is defined as the smallest set of FDs that
	# have the same closure as a given set of FDs.
	fdc, fds, attrs = fdclosure(fds, attrs)
	for ix in range(len(fds)-1, -1, -1):
		f = fds[ix].copy()
		del fds[ix]

		fdc1, fds, attrs = fdclosure(fds, attrs)

		if fdc1 == fdc:
			continue

		fds.append(f)

	return fds

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


#find minimal cover of FDs
fds = []
for fd in FinalFDs:
	fds.append([set(fd[0]),set(fd[1])])

FinalMinimalFDs = []
fds = minimalCover(fds, set(data2D.columns.tolist()))

for dependency in fds:
	FinalMinimalFDs.append(["".join(dependency[0]),"".join(dependency[1])])

#create custom name of output file
f = open("TANE_" + str(sys.argv[1]).split('.')[0] + "_results.txt", "w")

printAndWrite("Found total number of "+ str(len(FinalFDs))+ " FDs for the dataset "+ str(sys.argv[1])+ ".\n\nList of all FDs:",f)
FinalFDs.sort(key = FDSortIndex)
for fd in FinalFDs:
	printAndWrite(fd[0] + ' --> ' + fd[1],f)

printAndWrite("\nMinimal Cover (found " + str(len(FinalMinimalFDs)) + " dependencies):\n",f)
for fd in FinalMinimalFDs:
	printAndWrite(fd[0] + ' --> ' + fd[1],f)
f.close()