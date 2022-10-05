#!/usr/bin/python
# -*- coding: utf8 -*-

"""Important Note:
"""

from __future__ import print_function, division
from functools import reduce
import scipy as sp
import numpy as np

from nltk.stem import LancasterStemmer
from nltk.stem import PorterStemmer
 
import sys, re, codecs, time

from readontology import Ontology, output_str

try:
	import networkx as nx
except ImportError:
	print(InputError('networkx library not installed', 'networkx library ImportError on line 48 in \nconceptsimilarity.py source code\n\nInstall the networkx library and try again ...\n'))
	sys.exit(0)

Dict = {}

#
#	main
#

'''
General call:

$ python mappingvariable-jack.py <firstdataelementsetpath> <seconddataelementsetpath>

for example

$ python mappingvariable-jack.py ./input-data/TanzaniaElements.txt ./input-data/NigeriaElements.txt

'''

def main():

	firstdataelementsetpath = sys.argv[1]
	seconddataelementsetpath = sys.argv[2]

	scdoowlpath = './input-data/scdo.owl'
	mondoobopath = './input-data/mondo.obo'

	firstdataelementset = getsitevariables(firstdataelementsetpath, 0)
	seconddataelementset = getsitevariables(seconddataelementsetpath, 0)

	dataelementsets = [
			list(firstdataelementset.keys()),
			list(seconddataelementset.keys())]

	ontologies = [
		(scdoowlpath, None),
		(mondoobopath, None)]

	stime = time.time()
	OntoMap = ontologymapping(dataelementsets, ontologies)
	print("\nTime taken for ontology search is:", (time.time() - stime)/60, 'minutes')

	stime = time.time()	
	Mapping = semanticmapping(dataelementsets, OntoMap)
	print("\nTime taken for semantic mapping is:", (time.time() - stime)/60, 'minutes')

	numberofmatches = getnumberofdataelementmatches(Mapping)
	print("\nThe number of match is:", numberofmatches)


#
#	methods
#

def getsynonyms(ontfile, synonym = None):
	"""
	Searching through ontologies, similar word based on meaning or synonyms 
	for mapping synonym data elements from heterogeneous sources ...
	"""
	global Dict
	ontodata = Ontology(ontfile)
	exclusion_p = '\d+\w*\\.|\w*\d+\\.|\'|\"|_|-|,|;|\.|\?|:|%'
	if synonym:
		for k in ontodata:
			tt = str(k.id)
			key = ontodata[tt].name.lower().strip()
			key = re.sub(exclusion_p, " ", key)		
			key = key.split('(')[0].strip()
			if not key in Dict: Dict[key] = key
			for ss in ontodata[tt].other[synonym]:
				ssl = ss.lower().strip()
				ssl = ssl.split('(')[0].strip()
				if not ssl in Dict: Dict[ssl] = key					
	else:
		for k in ontodata:
			tt = str(k.id)
			key = ontodata[tt].name.lower().strip()
			key = re.sub(exclusion_p, " ", key)
			key = key.split('(')[0].strip()
			if not key in Dict: Dict[key] = key
			for ss in ontodata[tt].synonyms:
				ssl = ss.desc.lower().strip()
				ssl = ssl.split('(')[0].strip()
				if not ssl in Dict: Dict[ssl] = key
	#return Dict
	
def ontologymapping(DataElements, Ontologies):
	"""Takes lists of data elements and a list of onlogy files
       map data elements to ontology concept IDs where possible
	"""
	global Dict
	Mapping = {}

	# Get different ontology mapping
	for ontfile in Ontologies:
		readfile = getsynonyms(*ontfile)
	
	# Mapping different data elements in the codebook to ontology concept IDs
	exclusion_p = '\d+\w*\\.|\w*\d+\\.|\'|\"|_|-|,|;|\.|\?|:|%'
	Mapping = {}; n = 0; nset = len(DataElements)
	for varset in DataElements:
		for var in varset:
			core = re.sub(exclusion_p, " ", var)
			core = [s.strip() for s in core.strip().split('/')]
			core = [s.split('(')[0].strip().lower() for s in core]
			for ss in core:
				if ss in Dict:
					try: Mapping[Dict[ss]][n] = str(var)
					except:
						Mapping[Dict[ss]] = nset*[None]
						Mapping[Dict[ss]][n] = str(var)
		n += 1			
	del Dict
	return Mapping
	
def nlpconversion(DataElements):
	"""Return a word map dictionary and Adjacency matrix and words
	"""
	exclusion_p = '\d+\w*\\.|\w*\d+\\.|\'|\"|_|-|,|;|\.|\?|:|%'
	exclusion_a = '(?<!\S)a(?!\S)|(?<!\S)the(?!\S)|(?<!\S)of(?!\S)|(?<!\S)at(?!\S)|(?<!\S)in(?!\S)|(?<!\S)it(?!\S)|(?<!\S)on(?!\S)|(?<!\S)or(?!\S)|(?<!\S)and(?!\S)'
	Caster = LancasterStemmer()
	DataDict = {}
	G = nx.Graph()
	for varset in DataElements:
		for var in varset:
			if not var.strip(): continue
			content = re.sub(exclusion_p, " ", var)    	 			# deal with ponctuations
			content = re.sub(exclusion_a, "", content) 				# Exclude insignificant word
			content = content.strip().split('(')[0].strip()
			content = [Caster.stem(s.strip()) for s in content.strip().split()] # Find the root of word
			DataDict[var] = sorted(list(set(content[:])))
			nx.add_path(G,DataDict[var])
			del content
	
	A = nx.adjacency_matrix(G)
	return DataDict, G.nodes(), np.array(A.todense())

def semanticmapping(DataElements, ontosearch = {}):
	KeyMerge, Nodes, AdjMatrix = nlpconversion(DataElements)
	
	for el in KeyMerge: # Transforming to string for possible root lexical comparison
		if len(KeyMerge[el])==1: # remove s if it ends by 's' 
			KeyMerge[el] = KeyMerge[el][0] if not KeyMerge[el][0].endswith('s') else KeyMerge[el][0][:-1]
	
	n = AdjMatrix.shape
	
	Sim = np.identity(n[0])
	for i in range(n[0]):
		for j in range(i+1, n[0]):
			dst = sum(abs(AdjMatrix[i]-AdjMatrix[j]))/(sum(AdjMatrix[i])+sum(AdjMatrix[j]))
			Sim[i,j] = Sim[j,i] = 1 - dst

	del AdjMatrix

	# Generate the reference or harmonized data element set	
	HarmonizedMap = []
	n = len(DataElements)
	for i in range(n-1):
		FinalMapping = {}
		for key in ontosearch:
			if ontosearch[key][i]: 
				tmp = ontosearch[key][:]
				tmp.pop(i)
				FinalMapping[ontosearch[key][i]] = tmp[:]
		for j in range(i+1,n):
			for a in DataElements[i]:
				if not a.strip() or (a in FinalMapping and FinalMapping[a][j-1]): continue
				# Determine the most similar site-associated term
				iwords = KeyMerge[a]; ilen = len(iwords)
				adict = {}
				for b in DataElements[j]:
					if not b.strip(): continue
					jwords = KeyMerge[b]; jlen = len(jwords); ss = 0.0
					# Computing similarity between word sequences
					if isinstance(KeyMerge[a], list) and isinstance(KeyMerge[b], list): 
						au1 = [max([Sim[list(Nodes).index(s), list(Nodes).index(t)] for t in jwords]) for s in iwords]
						au2 = [max([Sim[list(Nodes).index(s), list(Nodes).index(t)] for t in iwords]) for s in jwords]
						ss = round((sum(au1)/ilen+sum(au2)/jlen)/2, 5)
					elif isinstance(KeyMerge[a], str) and isinstance(KeyMerge[b], str):
						# Computing similarity between words using lexical match
						ss = re.search(iwords, jwords) if ilen < jlen else re.search(jwords, iwords)
						ss = round(len(ss.group())/max(ilen, jlen),5) if ss else 0
					if ss >= 0.7: adict[b] = ss
					
				tmp = sorted(adict.items(), key = lambda x: x[1], reverse = True)
				for k in range(len(tmp)):
					if tmp[k][1]==1.0 and tmp[k][0]==a:
						tmp.insert(0, tmp[k])
						break
				try: FinalMapping[a][j-1] = tmp[0] if tmp else None
				except:
					FinalMapping[a] = (n-1)*[None]
					if tmp: FinalMapping[a][j-1] = tmp[0]
		# Update the harmonized map
		for a in FinalMapping: 
			satis = False; length = len(HarmonizedMap)
			for r in range(length):
				if HarmonizedMap[r][i]==a or (isinstance(HarmonizedMap[r][i], tuple) and HarmonizedMap[r][i][0]==a):
					satis = True
					refindx = i + 1
					for d in FinalMapping[a][i:]:
						if not HarmonizedMap[r][refindx]: HarmonizedMap[r][refindx] = d
						refindx += 1
					break
			if not satis:
				HarmonizedMap.append(n*[None])
				HarmonizedMap[-1] = FinalMapping[a][:i] + [a] + FinalMapping[a][i:]
					
	for a in DataElements[-1]:
		satis = False; length = len(HarmonizedMap)
		for r in range(length):
			if HarmonizedMap[r][-1]==a or (isinstance(HarmonizedMap[r][-1], tuple) and HarmonizedMap[r][-1][0]==a):
				satis = True
				break
		if not satis: # The data element 'a' is yet in the harmonized map and needs to be included
			 HarmonizedMap.append((n-1)*[None] + [a])
	# Creating standardized no-redundant data element set
	StandSet = set()		
	for a in HarmonizedMap:
		for elt in a:
			if elt:
				StandSet.add(elt[0]) if isinstance(elt, tuple) else StandSet.add(elt)
				break
#	for a in HarmonizedMap:
#		print(a)
	print("The length of Standardized dataset is:", len(StandSet))
	print("The number of elements in the harmonized map", len(HarmonizedMap))
	return HarmonizedMap		

def getsitevariables(SiteFiles, indx = 4):
	fp = codecs.open(SiteFiles, mode='r', encoding='utf-8-sig')
	header = fp.readline()
	DataDict = {}
	for line in fp:
		if not line.strip(): continue
		tline = [a.strip() for a in line.split('\t')]
		try:
			key = tline[indx]
			del tline[indx]
			DataDict[key] = tline[:]
		except: pass
		
	return DataDict


def getnumberofdataelementmatches(Mapping):
	n = 0
	for a in Mapping:
		test = reduce(lambda x, y: x*y, map(lambda x: x!= None, a))
		n += test
		if test: print(a)
	return numberofmatches


#
#	run main
#		
if __name__=='__main__':
	main()