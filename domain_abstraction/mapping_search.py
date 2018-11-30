# Author: Zeynep G. Saribatur
import sys
import os, glob
import subprocess
import time
import re
import random
from random import randint
import itertools
import csv

			
def checkFile(sets,logFile):

	arr=[]
	#print(sets)
	for i in range(0,len(sets)):
		checkfile=open(test+ '_check_answer'+str(i), 'w')
		logFile.write("In file "+ test+ "_check_answer"+str(i)+": "+ "\n")
		checkfile.write("%"+ sets[i])
		logFile.write("%"+ sets[i])
		sets[i]=sets[i][:sets[i].find("\n")]
		arr=sets[i].split(' ')
		checkfile.write("\n")
		logFile.write("\n")
		for j in range(0, len(arr)):
			if arr[j].find("mapTo")==-1 and arr[j].find("_")!=0 and arr[j].find("geq")==-1 and arr[j].find("less")==-1 and arr[j].find("equ")==-1 and arr[j].find("neq")==-1 and arr[j].find("leq")==-1:
				checkfile.write("absexists("+ arr[j] + "). ")
				logFile.write("absexists("+ arr[j] + "). ")
		checkfile.close()	
		logFile.write("\n")

	logFile.write("\n Step4 is done." + "\n")		
	logFile.write("\n")

def getCostOfMapping(test,mapping,pred,interestedelts,writer,index):
	global alloccurringabatoms
	logFile=open('log_search.txt','w')

	logFile.write("Running python program_dom_abstraction.py "+ test + ' ' + mapping + ' ' + pred + "\n")

	if interestedelts!=[]:		
		p= subprocess.Popen("python program_dom_abstraction.py {} ".format(test+ ' ' + mapping + ' ' + pred + ' '+interestedelts),
				shell=True, stdout=subprocess.PIPE, stderr=sys.stderr)
		output, err =p.communicate()
		p.wait()
	
	
		logFile.write("Running python program_dom_abstraction.py "+ test + ' ' + mapping + ' ' + pred + ' '+interestedelts+ "\n")
	else:
		p= subprocess.Popen("python program_dom_abstraction.py {} ".format(test+ ' ' + mapping + ' ' + pred),
				shell=True, stdout=subprocess.PIPE, stderr=sys.stderr)
		output, err =p.communicate()
		p.wait()
	
	temp=test+"_input"


	if os.path.isfile(temp)==True:
		temp1=test+"_input_abs"
		temp2=test+"_input_absfacts"
	else:
		temp=test
		temp1=test+"_abs"
		temp2=test+"_absfacts"

	logFile.write("Outputs: "+ temp1 + ' '+ temp2 + "\n")
	logFile.write("\n")

	try:
		with open(temp1) as f:
			f.close()
	except IOError:
		print(temp1+ " does not exist. ")

	else:
		clingo = subprocess.Popen(
			"clingo {} ".format(temp1+' '+temp2+' '+mapping),
			shell=True, stdout=subprocess.PIPE, stderr=sys.stderr)
		clingoout, clingoerr = clingo.communicate()
		#print(clingoout)
		del clingo
		clingoout = clingoout.decode('utf-8')
		#print (clingoout)
		logFile.write("Clingo is called with: "+ temp1 + ' '+ temp2 + ' '+ mapping+ "\n")
		logFile.write("Clingo output is: " + "\n")
		logFile.write(clingoout)
		logFile.write("Step2 is done." + "\n")
		logFile.write("\n")

		t=re.findall(r"CPU Time\ +: (\S*)s",clingoout)[0]
		writer[index].append(t)

		if clingoout.find('UNSATISFIABLE') != -1:
			print(test+" is unsatisfiable!")
			writer[index].append("-")
			writer[index].append("-")
			writer[index].append("UNSAT")
			print("testing the original program!")
			clingo = subprocess.Popen(
					"clingo {} ".format(test + ' aux_binaryrelations.lp aux_nonbinaryrelations.lp'),
					 shell=True, stdout=subprocess.PIPE, stderr=sys.stderr)
			clingoout, clingoerr = clingo.communicate()
			del clingo
			clingoout = clingoout.decode('utf-8')
			if clingoout.find('UNSATISFIABLE') == -1:
				print "PROGRAM IS ACTUALLY NOT UNSAT"
				logFile.write("PROGRAM IS ACTUALLY NOT UNSAT\n")
				sys.exit()
			t=re.findall(r"CPU Time\ +: (\S*)s",clingoout)[0]			
			writer[index].append(t)
			return -1
			#sys.exit()
		
		answersets=re.findall(r"(.*\n)", clingoout)

		for i in range (0,len(answersets)):
			if answersets[i]== "Answer: 1\n":
				start=i
			elif answersets[i]== "SATISFIABLE\n":
				end=i
		onlyanswersets=[answersets[k] for k in range(start+1,end) if "Answer:" not in answersets[k]]		
		checkFile(onlyanswersets,logFile)
		
		#logFile.write("Running python not_ab_atoms_new.py " + test+' '+pred + ' time'+"\n")
		logFile.write("Running python not_ab_atoms_new.py " + test+' '+pred +"\n")

		#p= subprocess.Popen("python not_ab_atoms_new.py {} ".format(test+' '+pred + ' time'),
		p= subprocess.Popen("python not_ab_atoms_new.py {} ".format(test+' '+pred),
			shell=True, stdout=subprocess.PIPE, stderr=sys.stderr)
		output, err =p.communicate()
		p.wait()

		#time.sleep(1)
		outputFile=test+"_ab"
		logFile.write("Output is: "+ outputFile + "\n")
		logFile.write("Step5 is done." + "\n")
		logFile.write("\n")

		try:
			with open(outputFile) as f:
				f.close()

		except IOError:
			print(outputFile+ " does not exist. ")
			sys.exit()
		else:
			cost=[]
			for i in range (0,len(onlyanswersets)):
				logFile.write("Clingo is called with: "+ outputFile+' '+temp+'_checkrules'+' '+test+ '_check_answer'+str(i)+ ' '+mapping+' aux_binaryrelations.lp aux_nonbinaryrelations.lp'+ "\n")
				clingo = subprocess.Popen(
					"clingo {} ".format(outputFile+' '+temp+'_checkrules'+' '+test+ '_check_answer'+str(i)+ ' '+mapping+' aux_binaryrelations.lp aux_nonbinaryrelations.lp'),
					 shell=True, stdout=subprocess.PIPE, stderr=sys.stderr)
				clingoout, clingoerr = clingo.communicate()
				#print(clingoout)
				del clingo
				clingoout = clingoout.decode('utf-8')
				print(clingoout)

				
				logFile.write("Clingo output is: " + "\n")
				logFile.write(clingoout)
				logFile.write("\n")

				
				t=re.findall(r"CPU Time\ +: (\S*)s",clingoout)[0]

				clingoLines=clingoout.split("\n")
				for k in range (0, len(clingoLines)):
					if clingoLines[k].find("OPTIMUM FOUND")!= -1:
						break
					if clingoLines[k].find("UNSATISFIABLE")!= -1:
						print("ANSWER IS UNSATISFIABLE, quitting...")
						sys.exit()
			
				if k==len(clingoLines)-1:
					print("No OPTIMUM FOUND, quitting...")
					sys.exit()
			
				if "ab" not in clingoLines[k-2]:
				#if clingoLines[k-1][-1]=="0" and clingoLines[k-1][-2]==" ":
					print("DONE! Found a solution to "+ test)
					logFile.write("DONE! Found a solution to "+ test)
					writer[index].append("0")
					writer[index].append(t)
					writer[index].append("SAT")
					cost=0
					print("testing the original program!")
					clingo = subprocess.Popen(
							"clingo {} ".format(test + ' aux_binaryrelations.lp aux_nonbinaryrelations.lp'),
							 shell=True, stdout=subprocess.PIPE, stderr=sys.stderr)
					clingoout, clingoerr = clingo.communicate()
					del clingo
					clingoout = clingoout.decode('utf-8')
					if clingoout.find('UNSATISFIABLE') != -1:
						print "PROGRAM IS ACTUALLY UNSAT"
						logFile.write("PROGRAM IS ACTUALLY UNSAT\n")
						sys.exit()
					t=re.findall(r"CPU Time\ +: (\S*)s",clingoout)[0]			
					writer[index].append(t)
					break
				else:
					abtext=clingoLines[k-2]
					costnum=abtext.count("ab")
					cost.append(costnum)
					writer[index].append(str(costnum))
					writer[index].append(t)
					writer[index].append("-")
					writer[index].append("-")
					abtext=abtext.split(" ")
					abtext=[re.findall(r"(\d+)",a) for a in abtext]
					#print abtext
					abtextnew=[a[1:] for a in abtext]
					#print abtextnew
					abtextnewnew=[list(set(a)) for a in abtextnew]
					#print abtextnewnew
					alloccurringabatoms=abtextnewnew
						

			#print cost
			return cost

def getRemainderCombination(test,arr,step,maxsizeref):
	if step>0:
		minsize=1
	else:
		minsize=len(arr)	
	if maxsizeref!=0:
		maxsize=maxsizeref
	else:
		maxsize=len(arr)
	for a in range(minsize,maxsize+1):
		listing = [list(x) for x in itertools.combinations(arr, a)]
		cameback=False
		#print "listing:"
		#print listing
		for b in range(0, len(listing)):
			test2=test+[listing[b]]
			#print test2
			remarr=[i for i in arr if i not in listing[b]]
			if a==1 and len(remarr)==1:
				test2=test2+[remarr]
				break
			if remarr!=[]:
				#print "vvvvvvvvvvvvvvvv"
				getRemainderCombination(test2,remarr,step-1,0)
				#print "^^^^^^^^^^^^^^^^"
				cameback=True
		if cameback==False:	
			global allprintedtests
			if sorted(test2) not in allprintedtests:
				allprintedtests.append(sorted(test2))
				#print sorted(test2)


def getRemainderSplit(test,arr,step):
	if step>0:
		minsize=1
	else:
		minsize=len(arr)	
	for a in range(minsize,len(arr)+1):
		listing = [arr[:a]]
		cameback=False
		#print "listing:"
		#print listing
		for b in range(0, len(listing)):
			test2=test+[listing[b]]
			#print test2
			remarr=arr[a:]
			if len(remarr)==1:
				test2=test2+[remarr]
				break
			if remarr!=[]:
				#print "vvvvvvvvvvvvvvvv"
				getRemainderSplit(test2,remarr,step-1)
				#print "^^^^^^^^^^^^^^^^"
				cameback=True
		if cameback==False:	
			global allprintedtests
			if sorted(test2) not in allprintedtests:
				allprintedtests.append(sorted(test2))
				#print sorted(test2)

def refineGivenCluster(arr,index,step):
	getRemainderCombination([],arr[index],step,1)
	print "---------------"
	global allprintedtests
	refinesteps=[]
	for j in range(0,len(allprintedtests)):
		refinesteps.append(len(allprintedtests[j])-1)
	for i in range(0,len(arr)):
		if i!=index:
			for j in range(0,len(allprintedtests)):
				allprintedtests[j]=sorted(allprintedtests[j]+[arr[i]])
	print "==========="
	print allprintedtests
	print "refinesteps:"
	print refinesteps
	print "==========="
	#sys.exit()
	return refinesteps


def refineGivenClusterSplit(arr,index,step):
	#print "refine "
	#print arr[index]
	getRemainderSplit([],arr[index],step)
	print "---------------"
	global allprintedtests
	refinesteps=[]
	for j in range(0,len(allprintedtests)):
		refinesteps.append(len(allprintedtests[j])-1)
	for i in range(0,len(arr)):
		if i!=index:
			for j in range(0,len(allprintedtests)):
				allprintedtests[j]=sorted(allprintedtests[j]+[arr[i]])
	print "==========="
	print allprintedtests
	print "refinesteps:"
	print refinesteps
	print "==========="
	return refinesteps

def createMappingFile(arr,filename,maxint,pred):
    
	text="dom("+pred+",1.."+str(maxint)+").\n"
	name=""
	for b in range(0, len(arr)):
		name=name+"_"
		if b<10:
			btemp="0_"+str(b)
		else:
			btemp="_".join(list(str(b)))
		for k in arr[b]:
			#text=text+"mapTo("+str(k)+",a"+str(b)+").\n"
			text=text+"mapTo("+pred+","+str(k)+",a"+str(btemp)+").\n"
			name=name+str(k)+"-"
		name=name[:len(name)-1]
	if filename=="":
		return text
	else:
		fout=open(filename,"w")
		fout.write(text)
		fout.close()

def processText(mappingtext):
	clusters=re.findall(r"\(\w+,(\d+)..(\d+),(\w+)\).",mappingtext)
	singlemaps=re.findall(r"\(\w+,(\d+),(\w+)\).",mappingtext)
	absdom1=list(set([c[2] for c in clusters]))
	absdom2=list(set([s[1] for s in singlemaps]))
	absdoms=sorted(list(set(absdom1+absdom2)))
	clustersAbs=[[] for i in range(len(absdoms))]
	maxint=0
	for c in clusters:
		arr=[]
		for i in range(int(c[0]),int(c[1])+1):
			arr.append(i)
		clustersAbs[absdoms.index(c[2])]+=arr
		if int(c[1])>maxint:
			maxint=int(c[1])
	for s in singlemaps:
		clustersAbs[absdoms.index(s[1])]+=[int(s[0])]
		if int(s[0])>maxint:
			maxint=int(s[0])
	return [clustersAbs,maxint]

def listOfListToText(m):
	text="%["
	for k1 in m:
		text=text+"["
		for k2 in k1:
			text=text+str(k2)+","
		#print text
		text=text[:len(text)-1]+"],"
	text=text[:len(text)-1]+"]\n"	
	return text

def countMostOccElt(arr,maxint):
	occcount=[0]*maxint
	for i in range(1,maxint+1):
		count=sum([x.count(str(i)) for x in arr])
		occcount[i-1]=count
	l = list(enumerate(occcount))
	sortedl = sorted(l, key=lambda x: -x[1])
	secondlargest = max([y for (x,y) in sortedl[1:]])
	onlylargest = [ (x,y) for (x,y) in sortedl if y >= secondlargest ]
	sampled= random.sample(onlylargest, 2)
	#print sampled
	return [sampled[0][0]+1,sampled[1][0]+1]

def existsInSameCluster(arr,focus):
	for a in arr:
		if focus[0] in a and focus[1] in a:
			return True
	return False

def alreadyInDiffClusters(arr,focus):
	for a in arr:
		if focus[0] in a and focus[1] in a:
			return False
	return True
	

def someInSingleCluster(arr,focus):
	if [focus[0]] in arr or [focus[1]] in arr:
		return True
	return False


def allInSingleCluster(arr,focus):
	if [focus[0]] in arr and [focus[1]] in arr:
		return True
	return False

def focusInCluster(arr,focus):
	print "--------checking if focus is here========="
	print arr
	print focus
	if focus[0] in arr or focus[1] in arr:
		return True
	return False

def refineToSingleClusters(arr,focus):
	arrtemp=[]
	for a in arr:
		if focus[0] not in a and focus[1] not in a:
			arrtemp.append(a)
			continue
		elif a==focus[0] or a==focus[1]:
			arrtemp.append(a)
			continue
		else:
			if focus[0] in a:
				temp1=a[:a.index(focus[0])]
				temp2=[focus[0]]
				temp3=a[a.index(focus[0])+1:]		
				if temp1!=[]:
					arrtemp.append(temp1)
				arrtemp.append(temp2)
				if temp3!=[]:
					arrtemp.append(temp3)
			elif focus[1] in a:
				temp1=a[:a.index(focus[1])]
				temp2=[focus[1]]
				temp3=a[a.index(focus[1])+1:]
				if temp1!=[]:
					arrtemp.append(temp1)
				arrtemp.append(temp2)
				if temp3!=[]:
					arrtemp.append(temp3)
	return arrtemp
				
	
	

test=sys.argv[1]
mapping=sys.argv[2]
pred= sys.argv[3]
refinetype= sys.argv[4]

realfilename=re.findall("([^/]+.lp)",test)[0]

csvfile= open("logfile_localsearch_"+realfilename[:len(realfilename)-3]+"_"+pred+".csv", 'w')
spamwriter=csv.writer(csvfile, delimiter=' ', quoting=csv.QUOTE_MINIMAL)
writer=[[]*8 for x in xrange(1000)]
writer[0].append("Name")
writer[0].append("Step")
writer[0].append("Mapping")
writer[0].append("Abs Answer Computation Time")
writer[0].append("Cost")
writer[0].append("Cost Computation Time")
writer[0].append("Result (Sat/Unsat)")
writer[0].append("Org Computation Time")
spamwriter.writerow(writer[0])


index=1

writer[index].append(realfilename)
writer[index].append("")
writer[index].append("")
writer[index].append("")
writer[index].append("")
writer[index].append("")
writer[index].append("")
spamwriter.writerow(writer[index])
index=index+1
writer[index].append(realfilename)

interestedelts=[]
if len(sys.argv) ==6:
	interestedelts=sys.argv[5]

for filename in glob.glob(test+"_*"):
    os.remove(filename) 

#read mapping from a file with mapTo, convert it to array of arrays
if os.path.isfile(mapping):
	fin=open(mapping,"r")
	mappingtext=fin.read()
	fin.close()
	[mapping,maxint]=processText(mappingtext)
else:
	#mapping=[[1], [2], [3], [4], [5], [6], [7], [8], [9], [10], [11], [12], [13], [14], [15], [16], [17], [18], [19], [20]]
	#mapping=[[1,2,3,4,5,6,7,8,9,10]]
	#mapping=[[1],[2],[3],[4,5,6,7],[8],[9],[10]]
	maxint=10
	arrray=[]
	for i in range(1,maxint+1):
		arrray+=[i]
	mapping=[arrray]
print mapping
print maxint

step=0
writer[index].append(str(step))
writer[index].append(listOfListToText(mapping))

filename="ex/generated_mappings/mapping_init.lp"
createMappingFile(mapping,filename,maxint,pred)
alloccurringabatoms=[]
cost=getCostOfMapping(test,filename,pred,interestedelts,writer,index)
print alloccurringabatoms
refinefocus= countMostOccElt(alloccurringabatoms,maxint)
print "refinefocus is " + str(refinefocus[0]) + " " +str(refinefocus[1])


spamwriter.writerow(writer[index])
index=index+1
writer[index].append(realfilename)
step=step+1

print mapping
print cost
if cost==0 or cost==-1:
	fout=open(test+"_result","w")
	fout.write(listOfListToText(mapping)+createMappingFile(mapping,"",maxint,pred))
	fout.close()
	sys.exit()

while True:
	picked=[False]*len(mapping)
	refinecosts=[[] for i in range(len(mapping))]

	allrefinements=[[] for i in range(len(mapping))]

	makesinglecluster=False
	if alreadyInDiffClusters(mapping,refinefocus) and allInSingleCluster(mapping,refinefocus)==False:
		print mapping
#		print refinefocus
		print "not some in single clusters" 
		makesinglecluster=True
		mapping=refineToSingleClusters(mapping,refinefocus)
		print mapping
		continue

	reffocus=[[] for i in range(len(mapping))]

	for j in range(0,len(mapping)):
		foundafocuscluster=False
		if len(mapping[j])==1:
			picked[j]=True
			continue
		elif picked[j]==False:
			foundafocuscluster=True
			randompick=j
		else:
			continue
		print "picking one by one"
		print mapping[randompick]
		allprintedtests=[]
		if refinetype=="0":
			refinesteps=refineGivenClusterSplit(mapping,randompick,1)
		elif refinetype=="1":
			refinesteps=refineGivenCluster(mapping,randompick,1)
		else:
			print "give a reasonable refinetype input!"
			sys.exit()



		print "----------------------refining with 1 step----------------------"
		for i in range(0,len(refinesteps)):
			if refinesteps[i]==1:
				nopossiblesinglecluster=False
				if existsInSameCluster(allprintedtests[i],refinefocus):
					print allprintedtests[i]
					print refinefocus
					print "exists in same cluster!" 
					continue
				if makesinglecluster and someInSingleCluster(allprintedtests[i],refinefocus)==False:
					print allprintedtests[i]
					print refinefocus
					print "not in single clusters" 
					nopossiblesinglecluster=True
					continue
				

				writer[index].append(str(step))
				writer[index].append(listOfListToText(allprintedtests[i]))				

				print allprintedtests[i]
				filename="ex/generated_mappings/mapping_refine_1.lp"
				createMappingFile(allprintedtests[i],filename,maxint,pred)
				alloccurringabatoms=[]
				cost=getCostOfMapping(test,filename,pred,interestedelts,writer,index)
				print alloccurringabatoms
				newrefinefocus= countMostOccElt(alloccurringabatoms,maxint)
				print "refinefocus could be " + str(newrefinefocus[0]) + " " +str(newrefinefocus[1])
				reffocus[j].append([newrefinefocus[0],newrefinefocus[1]])
					
				spamwriter.writerow(writer[index])
				index=index+1
				writer[index].append(realfilename)

				print cost
				if cost==0 or cost==-1:
					fout=open(test+"_result","w")
					fout.write(listOfListToText(allprintedtests[i])+createMappingFile(allprintedtests[i],"",maxint,pred))
					fout.close()
					print allprintedtests[i]
					sys.exit()
				refinecosts[j].append(cost)
				allrefinements[j].append(allprintedtests[i])
		
			
		picked[randompick]=True


	print allrefinements
	print refinecosts
	print reffocus

	mini=[]
	for i in range(0,len(refinecosts)):
		for j in range(0,len(refinecosts[i])):
			if mini==[]:
				mini=[refinecosts[i][j], (i,j)]
			else:
				if mini[0]>refinecosts[i][j]:
					mini=[refinecosts[i][j], (i,j)]
				elif mini[0]==refinecosts[i][j]:
					mini.append((i,j))

	print mini	
	if mini==[]:
		print "no further refinement will be done"
		break		
	randompick=randint(1, len(mini)-1)
	print "picked for refinement in random "+str(randompick)
	mapping=allrefinements[mini[randompick][0]][mini[randompick][1]]
	print mapping
	refinefocus=[reffocus[mini[randompick][0]][mini[randompick][1]][0],reffocus[mini[randompick][0]][mini[randompick][1]][1]]
	print "newrefinefocus is " + str(refinefocus[0]) + " " +str(refinefocus[1])

	
	step=step+1



