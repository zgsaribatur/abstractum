## Simge Demir, Sabanci University
## June, 2018
## program for adding no ab() atoms to the constraints 
## Updated/Fixed: Zeynep G. Saribatur

import re
import sys

def regex(atom,searchVariable):
	return re.findall(atom+r"\((\w+)\)",searchVariable)

def removeConstraint():
	#searches the constraints and ignores the one that does not include given atoms
	removal=[]
	for i in range(0,len(r1)):
		if r1[i].find("%") != -1:
			#print(r1[i])
			removal.append(r1[i])
		else:
			remove=True
			for x in range (2,len(sys.argv)):
				temp=regex(sys.argv[x],r1[i])
				if r1[i].find("}", r1[i].find(sys.argv[x])) != -1:
					print(r1[i] + " is not an appropriate constraint \n")
					#removal.append(r1[i])
					break
				elif len(temp)==0:
					print(r1[i] + " does not include the atom: "+ sys.argv[x] +"\n")
				elif len(temp)>0:
					print(r1[i] + " includes the atom: "+ sys.argv[x] +"\n")
					remove=False
			if remove==True:
				removal.append(r1[i])
				

	for element in range(0,len(removal)):
		r1.remove(removal[element])
		
def createNewline(i):
	newLine=""
	newLine+="\n{ab(r"+str(i)
	for y in range(0,len(r2)):
		if r2[y]=="-":
			continue
		newLine+="," + r2[y]
	newLine+=(") : ")
	countvars=0
	for x in range (2,len(sys.argv)):
		temp=regex(sys.argv[x],r1[i])
		#print "regexing "+sys.argv[x]
		#print(temp)
		if len(temp)==0:
			continue
		elif len(temp)==1:
			if x>2 and newLine[len(newLine)-2]!=":":					
				newLine+="," + sys.argv[x]+ "("+ r2[x-2+countvars] + ")"
			else:
				newLine+=sys.argv[x]+ "("+ r2[x-2+countvars] + ")"
		else:
			if x>2 and newLine[len(newLine)-2]!=":":
				newLine+="," + sys.argv[x]
				newLine+="("+ r2[x-2+countvars] + ")"
				for j in range(1,len(temp)):
					newLine+=","+ sys.argv[x]
					newLine+= "("+ r2[x-2+countvars+j] + ")"
				countvars=countvars+len(temp)-1
			else:
				newLine+=sys.argv[x]
				newLine+="("+ r2[x-2+countvars] + ")"
				for j in range(1,len(temp)):
					newLine+=","+ sys.argv[x]
					newLine+= "("+ r2[x-2+countvars+j] + ")"
				countvars=countvars+len(temp)-1
		#print "encountered "+str(countvars)+" traced vars so far"

	newLine+="}."
	#print (newLine)
	newLine2=""
	newLine2+="\n:~ ab(r" + str(i)
	for y in range(0,len(r2)):
		if r2[y]=="-":
			continue
		newLine2+="," + r2[y]
	newLine2+="). [1" 
	for y in range(0,len(r2)):
		if r2[y]=="-":
			continue
		newLine2+="," + r2[y]
	newLine2+=",r" +str(i)+ "]\n"
	
	#print (newLine2)		
	return newLine,newLine2
	
inputFile=sys.argv[1]
try:
	with open(inputFile) as f:
		lines=f.readlines()
	f.close()
except FileNotFoundError:
	print(inputFile+ " does not exist. ")
	
else:
	txt=""
	#getting the text in the file 
	for i in range (0,len(lines)):
		txt+=lines[i]
	#print (lines)

	## finding all the constraints in the .lp file
	r1=re.findall(r"(.*:-.*\.)\ *\%*.*",txt)
	print(r1)
	removeConstraint() ## removing the constraint if it does not include the given atom
	#print(r1)

	if len(r1)==0: ##if there is no constraint with the given atoms
		print("THERE IS NO CONSTRAINT WITH THE GIVEN ATOMS, OUTPUT FILE IS NOT CREATED")
		sys.exit()
	
	have4arg=False
	have5arg=False	
	have6arg=False

	for i in range(0,len(r1)):

		r2=[] ##list for the variables that will be written in not ab() atom.
		for x in range (2,len(sys.argv)):
			temp=regex(sys.argv[x],r1[i])
			if len(temp)==0:
				r2+="-"
			else:
				r2+=temp
		#print "----"
		#print(r2)
		#print "----"
		#print(lines)

		for k in range(0,len(lines)):
			if (lines[k][:lines[k].find(".")+1]== r1[i]): ##finding the constraint in the file
				#print(lines[k])
				##adding not ab() atoms 
				r1[i]=r1[i].replace(".",",")
				r1[i]+= "not ab(r" +str(i)
				for y in range(0,len(r2)):
					if r2[y]=="-":
						continue
					r1[i]+= "," + r2[y]  
				r1[i]+= ")." + "\n"	
				lines[k]=r1[i]##changing the line with the new one which is overwritten with not ab()
				
				print r1[i]
				## adding the following new line at the end:
				## {ab(r#,T,T1) : timea(T),timea(T1)}.
				#print (newLine)
				newline,newline2=createNewline(i)
				lines.append(newline) 

				##adding the second new line:	
				#:~ ab(r#,T,T1). [1,T,T1,r#]
				lines.append(newline2)

				if re.search(r'ab\(\w+,\w+,\w+,\w+\)',newline2):
					have4arg=True
				elif re.search(r'ab\(\w+,\w+,\w+,\w+,\w+\)',newline2):
					have5arg=True
				elif re.search(r'ab\(\w+,\w+,\w+,\w+,\w+,\w+\)',newline2):
					have6arg=True
					

	lines.append("\n#show ab/2.\n")
	lines.append("#show ab/3.\n")

	if have4arg==True:
		lines.append("#show ab/4.\n")
	if have5arg==True:
		lines.append("#show ab/5.\n")
	if have6arg==True:
		lines.append("#show ab/6.\n")
	
	## creating the output file and writing the last version of the text 
	outputFile=inputFile+"_ab"
	out=open(outputFile,'w')

	for i in range (0,len(lines)):
		out.write(lines[i])
