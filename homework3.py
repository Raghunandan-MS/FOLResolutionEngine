import os
import re
import copy
import time

KB = []
pattern = r'([\~]?\w[\w]*)\((.*)\)$' # To be able to match the predicat and the specified parameters to the predicate in FOL
outputDict = {}

def readInput():
	global KB
	queryList = []
	KBList = []

	input_file = open('input.txt', 'r')
	inputParams = input_file.readlines()
	input_file.close()

	queryArgs = inputParams[0: int(inputParams[0]) + 1]
	KBArgs = inputParams[int(inputParams[0]) + 1::]

	for i in range(1, len(queryArgs)):
		queryList.append(queryArgs[i].rstrip('\n'))
	for i in range(1, len(KBArgs)):
		KBList.append(KBArgs[i].rstrip('\n'))

	convertToCNF(KBList)
	outputString = ''
	for query in queryList:
		queryResult = resolutionAlgorithm(KB, query)
		outputString = outputString + queryResult + '\n'
	outputString = outputString[0:len(outputString) - 1]
	output_file = open('output.txt' , 'w')
	output_file.write(outputString)
	output_file.close()

def resolutionAlgorithm(KB, alpha):
	# Returns true or false.
	clauses = copy.deepcopy(KB)
	clauses.append(negateLiteral(alpha))
	new = set()
	while True:
		for i in range(len(clauses)):
			for j in range(i+1, len(clauses)):
				resolvents = resolveSentences(clauses[i], clauses[j])
				if 'JUNK' in resolvents:
					return 'TRUE'
				new = new.union(resolvents)
		if new.issubset(set(clauses)):
			return 'FALSE'
		clauses = list(set(clauses).union(new))

def resolveSentences(sentenceA, sentenceB):
	sentenceSplitA = sentenceA.split(' | ')
	sentenceSplitB = sentenceB.split(' | ')
	formulasInferred = set()
	for litA in sentenceSplitA:
		for litB in sentenceSplitB:
			if ('~' in litA and '~' not in litB) or ('~' not in litA and '~' in litB): #and (not ('~' in litA and '~' in litB)):
				theta = unifyLists(litA, litB, {})
				if theta != 'FAILURE':
					unifiedSentenceA = applySubstitution(theta, sentenceA)
					unifiedLitA = applySubstitution(theta, litA)
					unifiedSentenceB = applySubstitution(theta, sentenceB)
					unifiedLitB = applySubstitution(theta, litB)
					sentenceC = unifiedSentenceA.difference(unifiedLitA).union(unifiedSentenceB.difference(unifiedLitB))
					sentenceC = ' | '.join(list(sentenceC))
					if len(sentenceC) == 0:
						formulasInferred.add('JUNK')
					else:
						formulasInferred.add(sentenceC)
	return formulasInferred

def applySubstitution(theta, sentence):
	global pattern
	splitVal = sentence.split(' | ')
	tempList = []
	for i in range(len(splitVal)):
		predicate, params = re.match(pattern, splitVal[i]).groups()
		paramsSplit = params.split(',')
		for i in range(len(paramsSplit)):
			tempVar = paramsSplit[i]
			if tempVar.islower() and tempVar in theta.keys():
				paramsSplit[i] = paramsSplit[i].replace(tempVar, theta[tempVar])
		params = ','.join(paramsSplit)
		tempList.append(predicate + '(' + params + ')')
	return set(tempList)

def unifyLists(litA, litB, theta):
	global pattern
	predA, argsA = re.match(pattern, litA).groups()
	predB, argsB = re.match(pattern, litB).groups()
	argsSplitA = argsA.split(',')
	argsSplitB = argsB.split(',')
	if '~' in predA:
		predA = predA[1:]
	elif '~' in predB:
		predB = predB[1:]
	if predA != predB or (len(argsSplitA) != len(argsSplitB)):
		return 'FAILURE'
	for i in range(len(argsSplitA)):
		termA = argsSplitA[i]
		termB = argsSplitB[i]
		theta = unifyTerms(termA, termB, theta)
		if theta == 'FAILURE':
			return 'FAILURE'
	return theta

def unifyTerms(termA, termB, theta):
	while termA.islower() and theta.get(termA, False):
		termA = theta[termA]
	while termB.islower() and theta.get(termB, False):
		termB = theta[termB]
	if termA == termB:
		pass
	elif termA.islower():
		theta[termA] = termB
	elif termB.islower():
		theta[termB] = termA
	elif not termA.islower() or not termB.islower():
		theta = 'FAILURE'
	else:
		theta = unifyLists(termA, termB, theta)
	return theta

def convertToCNF(sentences):
	# 3 types of variants to be handeled here.
	# 1. p1 & p1 & p3 => q / ~q (Remove implication and handle the changes)
	# 2. p1 & p2 (Consider each of them as seperate literals)
	# 3. P(x,y)

	global KB

	for sentence in sentences:
		if '=>' in sentence:
			implicationList = sentence.split(' => ')
			consequent = implicationList[-1]
			premise = implicationList[0]
			string = negateAndConvert(premise)
			KB.append(string + ' | ' + consequent)
		elif '&' in sentence:
			literalSplit = sentence.split(' & ')
			for val in literalSplit:
				KB.append(val)
		else:
			KB.append(sentence)

def negateAndConvert(premiseList):
	literals = premiseList.split(' & ')
	tempList = []
	for literal in literals:
		tempList.append(negateLiteral(literal))
	string = ' | '.join(tempList)
	return string

def negateLiteral(literal):
	if '~' in literal:
		return literal[1:]
	else:
		return '~' + literal

if __name__ == '__main__':
	start = time.time()
	readInput()
	end = time.time()
	print ("Time taken is : ", end - start)