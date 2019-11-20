import math
import random
import re
import os
from collections import deque

# A global dictionary called KB. This will be used similar to a HashMap!.

KB = {}
pattern = r'([\~]?\w[\w]*)\((.*)\)$' # To be able to mathc the predicat and the specified parameters to the predicate in FOL
outputDict = {}

def readInput():
	queryList = []
	KBList = []
	cnfList = []

	file = open('input.txt', 'r')
	inputParams = file.readlines()

	file.close()
	queryArgs = inputParams[0: int(inputParams[0]) + 1]
	KBArgs = inputParams[int(inputParams[0]) + 1::]

	for i in range(1, len(queryArgs)):
		queryList.append(queryArgs[i].rstrip('\n'))
	for i in range(1, len(KBArgs)):
		KBList.append(KBArgs[i].rstrip('\n'))

	# Call the helper functions to conver all the sentences from INF to CNF.
	changeSentenceForm(KBList, cnfList)
	# Parse the list of cnf literals and store each of the predicate in the KB. Common elements of the cnf will have the same cnf
	populateKB(cnfList)
	print (KB)
	# Using Regex to get predicate name and all parameters for resolution and unification step!
	# Take the negation of the query and search the KB for the specified negation.
	result = inferFromKB(queryList)
	outputString = ''
	for keys in result.keys():
		outputString = outputString + result[keys] + '\n'
	# Write the output to the file.
	output_file = open('output.txt', 'w')
	output_file.write(outputString[0:len(outputString) - 1])
	output_file.close()

def changeSentenceForm(KBList, cnfList):
	for i in range(len(KBList)):
		cnfList.append(convertToCNF(KBList[i]))

def convertToCNF(string):
	if '=>' in string:
		convertedString = buildCNFSentence(string)
		# Use the converted String to store it into the KB.
		# If the string is a clause (disjunction), iterate over each predicate and store the value in the KB.
		# If it is a single predicate literal, check if the KB has a predicate.
		# If yes, add the new variables, ground terms to it.
		# If not, create a new entry in the table and add the relevant details to it!
		return convertedString
	else:
		return string

def buildCNFSentence(string):
	#Split at the implication sign and add an 'OR' operator
	sentence = string.split(' => ')
	consequent = sentence[-1] # Assigning the last term as a consequent. Others are all premise.
	premise = negatePremise(sentence[0].split(' & '))
	modifiedSentence = premise + ' | ' + consequent
	return modifiedSentence

def negatePremise(sentence):
	# If the premise is only a single predicate P(x,y), you can just return the string with a negated value attached.
	# Split on the 'AND' symbol and then concatinate them with the 'OR' operator.
	tempString = ''
	if len(sentence) == 1 and '~' not in sentence[0]:
		return '~' + sentence[0]
	elif len(sentence) == 1:
		return sentence[0][1:]
	else:
		sentence = ['~' + sentence[i] if '~' not in sentence[i] else sentence[i][1:] for i in range(len(sentence))]
		return ' | '.join(sentence)

def populateKB(cnfList):
	global pattern
	global KB
	for i in cnfList:
		literals = i.split(' | ')
		for literal in literals:
			predicate, params = re.match(pattern, literal).groups()
			if predicate not in KB.keys():
				KB[predicate] = {}
				KB.get(predicate).update({'params': [params], 'cnf': [i]})
			else:
				KB.get(predicate)['params'].append(params)
				if i not in KB.get(predicate)['cnf']:
					KB.get(predicate)['cnf'].append(i)

def inferFromKB(queries):
	global outputDict
	for query in queries:
		flag = False
		counter = 1
		if counter == 1:
			query = negateTerm(query)
		resolutionString = resolutionStep(negateTerm(query))
		counter += 1
		if resolutionString == 'FAIL':
			flag = True
		# Modify the length of the resolution string to ensure that resolution was successful.
		while len(resolutionString) != 0 and resolutionString != 'FAIL':
			# There are strings still to be resolved.
			searchString = resolutionString
			searchStringSplit = searchString.split(' | ')
			if len(searchStringSplit) == 1:
				resultString = resolutionStep(negateTerm(searchStringSplit[0]))
				if resultString == '':
					# The same query was present in the KB, and query was a single literal, it can be resolved.
					resolutionString = resultString
				elif resultString == 'FAIL':
					# No unificatio was possible
					flag = True
					outputDict[query] = 'FALSE'
					resolutionString = ''
				else:
					# Will expect a cnf literal of more than 1 clause.
					resolutionString = resultString
			elif len(searchStringSplit) > 1:
				for searchQuery in searchStringSplit:
					resultString = resolutionStep(negateTerm(searchQuery))
					if resultString == 'FAIL':
						# Continue with other literals.
						flag = True
						continue
					elif resultString == '':
						# Continue resolution with other remaining literals
						resolutionString = ' | '.join([searchStringSplit[i] for i in range(len(searchStringSplit)) if searchQuery != searchStringSplit[i]])
						flag = False
					else:
						# You received a CNF Form resolved sentence. Set the resolution string to it.
						resolutionString = resultString
			elif counter > 100:
				flag = True
				outputDict[query] = 'FALSE'
			counter += 1
		if flag:
			outputDict[query] = 'FALSE'
		else:
			outputDict[query] = 'TRUE'
	return outputDict

def resolutionStep(query):
	global pattern
	global KB
	predicate, argument = re.match(pattern, query).groups()
	#print ("Params received and calculated are : ", query, predicate, argument)
	# Retrieve the set of all possible sentences and their respective parameters from the KB.
	cnfSentence, params = KB.get(predicate)['cnf'], KB.get(predicate)['params']
	# You may or may not get multiple list of sentences.
	# Check for unification and resolution for each and every sentence.
	if query in cnfSentence:
		# Check if query is single or not.
		# Replace only the matched string in the current query and return.
		return ''
	for i in range(len(cnfSentence)):
		# Try to unify with this sentence and it's respective parameters.
		# Call unify query with parameters of this sentence.
		subsList = unifyQuery(argument, params[i])
		resolvedString = ''
		if subsList == 'FAIL':
			# Try to find the next possible parameter / string combination where you can unify this string.
			#resolvedString = 'FAIL'
			continue
		elif subsList:
			# This sentence was unifiable and I can replace the values in the sentence and return the resolved sentence.
			sentenceSplit = cnfSentence[i].split(' | ')
			tempList = []
			# For each part in the multiple disjuncton literal.
			for j in range(len(sentenceSplit)):
				# Get the predicate name and parameters to be replaced for this string.
				pred, args = re.match(pattern, sentenceSplit[j]).groups()
				for keys in subsList.keys():
					if keys in args:
						args = args.replace(keys, subsList[keys])
				# After replacing all the values, you will need to create the new predicate with the unified values.
				if pred != predicate:
					tempList.append(pred + '(' + args + ')')
			# Create the new resolved string and return back this value.
			# We need not iterate over all the other values in the cnfSentence.
			resolvedString = ' | '.join(tempList)
		return resolvedString
	# No unification or resolution was possible and hence we return FAIL.
	return 'FAIL'

def unifyQuery(resolutionArgs, sentenceArgs):
	# First Argument : Arguments of the given string to be resolved.
	# Second Argument: Parameters of each and every sentence.
	subsList = {} # Key value pairs to resolve the string.
	if len([resolutionArgs]) == len([sentenceArgs]):
		resolutionArgsSplit = resolutionArgs.split(',')
		sentenceArgsSplit = sentenceArgs.split(',')
		for i in range(len(resolutionArgsSplit)):
			if resolutionArgsSplit[i][0].isupper() and sentenceArgsSplit[i][0].islower():
				subsList[sentenceArgsSplit[i]] = resolutionArgsSplit[i]
			elif resolutionArgsSplit[i][0].isupper() == sentenceArgsSplit[i][0].isupper() and (sentenceArgsSplit[i] != resolutionArgsSplit[i]):
				# Strings are not equal, so we need not go further to check subsList.
				# Return a value indicating we cannot create a subsList.
				return 'FAIL'
			elif resolutionArgsSplit[i][0].islower() and sentenceArgsSplit[i][0].isupper():
				subsList[sentenceArgsSplit[i]] = resolutionArgsSplit[i]
	else:
		# Lengths are not equal and it is not possible to substitute the values.
		return 'FAIL'
	return subsList

def negateTerm(string):
	if '~' not in string:
		string = '~' + string
	else:
		string = string[1:]
	return string

if __name__ == "__main__":
	readInput()