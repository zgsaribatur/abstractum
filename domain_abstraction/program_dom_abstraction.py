# Author: Zeynep G. Saribatur
# shifting more than one literal at the same time
# there can be diff variables from diff domains which are not abstracted
# deal with treating the odd loops specially
# shifts for all neg's with nonsingleton clusters
# deal with choice rule with a pre-process before calling the meta and put them back with a post-process
# if there are constants in the rule, then need to change them to the mapped abstract value!
# TODO having rel using vars from diff domains -> this is omitted for now
# instead of having <,<=,>= in abs prog. need to have less,leq,geq as the binary relation may not be defined over the abs values!!!
# non binary relations


import re
import pexpect
import time
import sys
import csv
import string
import os
import itertools

class meta:
	def __init__(self,textOrg,sp,dap,absinfo):
		self.rules=re.findall(r"rule\((\S+)\).",textOrg)
		self.head=re.findall(r"head\((\S+),\ *(\S+)\).",textOrg)
		self.negbody=re.findall(r"negbody\((\S+),\ *(\S+)\).",textOrg)
		self.posbody=re.findall(r"posbody\((\S+),\ *(\S+)\).",textOrg)
		self.pred=re.findall(r"pred\((\S+),\ *(\S+)\).",textOrg)
		self.struct=re.findall(r"struct\((\S+),\ *(\d+),\ *(\S+),\ *(\S+)\).",textOrg)
		self.arity=re.findall(r"arity\((\S+),\ *(\d+)\).",textOrg)
		self.var=re.findall(r"var\((\S+),\ *(\S+)\).",textOrg)
		self.atoms=[]
		self.predList=[]
		self.ruleRel=[]
		self.sharesRelPlus=[]
		self.sharesRelMinus=[]
		self.predRelVar=[]
		self.predRelVarNonBin=[]
		self.specialPreds=sp
		self.facts=[]
		self.factPreds=[]
		self.absAtoms=[]
		self.cyclicDep=[]
		self.atomPredList=[]
		self.atomList=[]
		self.domAbsPred=dap
		self.mapping=absinfo[0]
		self.abstractedAtoms=[]
		self.inputPredsRelatedWithAbs=[]


	def initializeAtoms(self):
		self.getFacts()
		atomlist=[]
		for pr in self.pred:
			if pr[0] in self.factPreds:
				#print self.factPreds
				fact=True
				exists=True
				textAbsAtom=pr[1]+"("
			else:
				fact=False
				if pr[1]!="equ" and pr[1]!="neq" and pr[1]!="less" and pr[1]!="geq" and pr[1]!="greater" and pr[1]!="leq" and pr[1]!="plus" and pr[1]!="neqEqu" and pr[1]!="equEqu" and pr[1]!="neqNeq" and pr[1]!="leqLeq" and pr[1]!="leqLess" and pr[1]!="lessLess" and pr[1]!="leqEqu":
					exists=False
					#print atomlist
					for k in atomlist:
						#print "have at hand "+pr[0] + " " + pr[1]
						#print "checking with "+k
						if k==pr[1] and self.checkIfPredHasNonDomAbsArg(pr[0])==False:# or pr[1] in self.inputPredsRelatedWithAbs:
							exists=True
							break
					if exists==False:
						atomlist.append(pr[1])
						textCheckAtom=pr[1]+"("
						#print textCheckAtom
				else:
					exists=True
			if pr[1]=="equ" or pr[1]=="neq" or pr[1]=="less"  or pr[1]=="geq" or pr[1]=="greater" or pr[1]=="leq":
				var1=""
				var2=""
			elif pr[1]=="plus" or pr[1]=="equEqu" or pr[1]=="neqEqu" or pr[1]=="neqNeq" or pr[1]=="leqLeq" or pr[1]=="leqLess" or pr[1]=="lessLess" or pr[1]=="leqEqu":
				var1=""
				var2=""
				var3=""
				var4=""
			else:
				textAtom=pr[1]+"("
			argtemp=m.getArgs(pr[0])
			noneedtoadd=False
			if argtemp!=[]:
				index=1
				argHasNotVar=False
				#for arg in argtemp:	
				for ii in range(0,len(argtemp)):
					arg=argtemp[ii]			
					if re.search('v[A-Z]', arg)!=None:
						arg=arg.replace("v","")
					if pr[1]=="equ" or pr[1]=="neq" or pr[1]=="less" or pr[1]=="greater" or pr[1]=="geq" or pr[1]=="leq":
						if var1=="":
							var1=arg
						else:
							var2=arg
							if pr[1]=="equ":
								textAtom=var1+"="+var2
								#textAtom="equ("+var1+","+var2+")"
							if pr[1]=="neq":
								textAtom=var1+"!="+var2
								#textAtom="neq("+var1+","+var2+")"
							if pr[1]=="less":
								textAtom=var1+"<"+var2
								#textAtom="less("+var1+","+var2+")"
							if pr[1]=="greater":
								textAtom=var1+">"+var2
							if pr[1]=="geq":
								textAtom=var1+">="+var2
								#textAtom="geq("+var1+","+var2+")"
							if pr[1]=="leq":
								textAtom=var1+"<="+var2
								#textAtom="leq("+var1+","+var2+")"
							self.predRelVar.append([pr[0], pr[1], var1, var2])
					elif pr[1]=="plus" or pr[1]=="equEqu" or pr[1]=="neqEqu" or pr[1]=="neqNeq" or pr[1]=="leqLeq" or pr[1]=="leqLess"  or pr[1]=="lessLess" or pr[1]=="leqEqu":
						if var1=="":
							var1=arg
						elif var2=="":
							var2=arg
						elif var3=="":
							var3=arg
							if len(argtemp)==3:
								textAtom=pr[1]+"("+var1+","+var2+","+var3+")"
								self.predRelVarNonBin.append([pr[0], pr[1], var1, var2, var3])
						else:
							var4=arg
							textAtom=pr[1]+"("+var1+","+var2+","+var3+","+var4+")"
							self.predRelVarNonBin.append([pr[0], pr[1], var1, var2, var3, var4])
						
					else:
						#FIXME this is to deal with replaced time variables - make it better 
						if arg=="TPLUS1":
							argreplace="T+1"
						elif arg=="TMINUS1":
							argreplace="T-1"
						else:
							argreplace=arg
						textAtom=textAtom+argreplace+","
						if fact==True:
							#it's a fact but does it have abstracted arguments?
							#a function to check if fact has relation to domabs
							#print "checking fact"
							#print pr
							ans=self.checkFactHasAbs(pr[1],ii)
							if True in ans:
								textAbsAtom=textAbsAtom+"X"+ans[1].upper()+str(index)+","
							else:
								textAbsAtom=textAbsAtom+arg+","
						if exists==False:
							#print pr[0]
							rulename=re.findall(r"(r\d+)[bh]",pr[0])[0]
							ans=self.checkArgExistInAbsPred(rulename,arg)
							if False in ans:
								#print arg + " do not exist in abs pred "+rulename
								textCheckAtom=textCheckAtom+arg+","
								if re.search(r"[A-Z]",arg[0])==None:
									argHasNotVar=True
							else:
								textCheckAtom=textCheckAtom+"X"+ans[1].upper()+str(index)+","
					index=index+1				
				if pr[1]!="equ" and pr[1]!="neq" and pr[1]!="less" and pr[1]!="geq" and pr[1]!="greater" and pr[1]!="leq" and pr[1]!="plus":
					textAtom=textAtom[:len(textAtom)-1]+")"	
					if fact==True:
						textAbsAtom=textAbsAtom[:len(textAbsAtom)-1]+")"
					if exists==False:
						textCheckAtom=textCheckAtom[:len(textCheckAtom)-1]+")"	
						if argHasNotVar==False and pr[1] in atomlist:
							if self.checkIfAlreadyExistsWithVars(len(argtemp),self.atomList,pr[1])==True:
								noneedtoadd=True
			else:
				textAtom=textAtom[:len(textAtom)-1]
				if fact==True:
					textAbsAtom=textAbsAtom[:len(textAbsAtom)-1]	
				if exists==False:
					textCheckAtom=textCheckAtom[:len(textCheckAtom)-1]	
			self.atoms.append([pr[0],textAtom])
			if fact==True:
				self.absAtoms.append([pr[0],textAbsAtom])
			if exists==False:
				if noneedtoadd==False:
					self.atomList.append([pr[0],textCheckAtom])
				else:
					atomlist=atomlist[:len(atomlist)-1]
		self.atomList=[a[1] for a in self.atomList]
		print self.atomList
		for ar in self.arity:
			self.predList.append(ar[0])
		self.obtainRel()

	def printout(self):
		print "------------"
		#print self.rules
		#print self.head
		#print self.negbody
		#print self.posbody
		#print self.pred
		#print self.struct
		#print self.arity
		#print self.var
		#print self.facts
		#print self.factPreds
		#print self.absAtoms
		#print "initialized"
		#print self.atoms
		#print self.predList
		#print self.predRelVar
		#print self.predRelVarNonBin
		#print "rel rule"
		#print self.ruleRel
		#print "S^+ rel rule"
		#print self.sharesRelPlus
		#print "S^- rel rule"
		#print self.sharesRelMinus
	
	def getPred(self,p): 
		return [a[1] for a in self.pred if a[0]==p][0]
	def getHead(self,r):
		h=[a[1] for a in self.head if a[0]==r]
		if h==[]:
			h=[[]]
		return h 
	def getPosbody(self,r):
		return [a[1] for a in self.posbody if a[0]==r] 
	def getNegbody(self,r):
		return [a[1] for a in self.negbody if a[0]==r] 
	def getArity(self,p):
		return int([a[1] for a in self.arity if a[0]==p][0])
	def getArgs(self,p):
		return [a[3] for a in self.struct if a[0]==p] 
	def getType(self,p):
		return [a[2] for a in self.struct if a[0]==p][0] 
	def getPredSym(self,p):
		return [a[0] for a in self.pred if a[1]==p]
	
	
	def getAtom(self,r):
		return [a[1] for a in self.atoms if a[0]==r]

	def getSplus(self,r):
		return [a[1] for a in self.sharesRelPlus if a[0]==r]
	def getSminus(self,r):
		return [a[1] for a in self.sharesRelMinus if a[0]==r]

	#FIXME we already know the isCluster ones
	def getNonSingletonClusters(self):
		absvalues=list(set([m[1] for m in self.mapping]))
		count=[0]*len(absvalues)
		for m in self.mapping:
			for i in range(0,len(absvalues)):
				if m[1]==absvalues[i]:
					count[i]=count[i]+1
					break
		return [k for k in absvalues if count[absvalues.index(k)]>1]

	def checkIfAlreadyExistsWithVars(self,n,arr,pred):
		searchtext="\A"+pred+"\([A-Z][A-Za-z]*\d*"
		for i in range(1,n):		
			searchtext=searchtext+",\ *[A-Z][A-Za-z]*\d*"
		for a in arr:
			#print searchtext
			#print a
			if re.search(searchtext,a[1])!=None:
				return True
		return False

	def obtainRel(self):
		for a in self.rules:
			foundrel=False
			for b in self.pred:
				if a+"b" in b[0] and (b[1]=="equ" or b[1]=="neq" or b[1]=="less" or b[1]=="greater" or b[1]=="geq" or b[1]=="leq"  or b[1]=="plus" or b[1]=="neqEqu" or b[1]=="equEqu" or b[1]=="neqNeq" or b[1]=="leqLeq" or b[1]=="leqLess" or b[1]=="lessLess" or b[1]=="leqEqu"):
					self.ruleRel.append([a,b[0],b[1]])
					foundrel=True
					reltemp=b[0]
			if not foundrel:
				self.ruleRel.append([a,"none","none"])
			else:
				for b in self.getPosbody(a):
					if b!=reltemp and self.getPred(b) not in self.specialPreds:
						#print m.getPred(b)
						ret=self.checkVarShare(b,reltemp)
						if ret!=[]:
							for c in ret:
								self.sharesRelPlus.append([a,b])
				for b in self.getNegbody(a):
					if b!=reltemp and self.getPred(b) not in self.specialPreds:
						#print m.getPred(b)
						ret=self.checkVarShare(b,reltemp)
						if ret!=[]:
							for c in ret:
								self.sharesRelMinus.append([a,b])

	def getFacts(self):
		for a in self.rules:
			if self.getPosbody(a)==[] and self.getNegbody(a)==[]:
				self.facts.append(a)
				#FIXME for now assuming head has one atom!
				self.factPreds.append(self.getHead(a)[0])
	

	def checkVarShare(self,a,b):
		aVarList=[k[3] for k in self.struct if k[0]==a and k[2]=="var"]
		bVarList=[k[3] for k in self.struct if k[0]==b and k[2]=="var"]
		#print "checking var share" 
		#print a, b
		#print aVarList, bVarList
		return list(set(aVarList) & set(bVarList))

	def checkRelatedWithRuleRel(self,relinfo,rulerelpred):
		#print relinfo
		#print rulerelpred
		relpredinfo=[k for k in self.predRelVar if k[0]==rulerelpred]
		if relpredinfo==[]:
			#print self.predRelVarNonBin
			relpredinfo=[k for k in self.predRelVarNonBin if k[0]==rulerelpred][0]
		else:
			#print self.predRelVar
			relpredinfo=relpredinfo[0]
		#print relpredinfo
		firstHasVar=re.match(r'[A-Za-z]',relpredinfo[2]) 
		secondHasVar=re.match(r'[A-Za-z]',relpredinfo[3])
		if not firstHasVar:
			num=re.findall(r'(\d+)',relpredinfo[2])[0]
			for m in self.mapping:
				if m[0]==str(num) and m[1]!=relinfo[1]:
					return False
		#print "either has first var or has mapping" 
		if not secondHasVar:
			#print self.mapping
			num=re.findall(r'(\d+)',relpredinfo[3])[0]
			#print num
			#print relinfo[2]
			for m in self.mapping:
				if m[0]==str(num) and m[1]!=relinfo[2]:
					return False
		#print "either has second var or has mapping" 
		if len(relinfo)>4:
			if len(relpredinfo)!=len(relinfo):
				return False
			thirdHasVar=re.match(r'[A-Za-z]',relpredinfo[4])
			if not thirdHasVar:
				num=re.findall(r'(\d+)',relpredinfo[4])[0]
				for m in self.mapping:
					if m[0]==str(num) and m[1]!=relinfo[3]:
						return False
		if len(relinfo)>5:
			if len(relpredinfo)!=len(relinfo):
				return False
			fourHasVar=re.match(r'[A-Za-z]',relpredinfo[5])
			if not fourHasVar:
				num=re.findall(r'(\d+)',relpredinfo[5])[0]
				for m in self.mapping:
					if m[0]==str(num) and m[1]!=relinfo[4]:
						return False
		return True
			
			
	
	def checkArgExistInAbsPred(self,r,arg):
		posbody=self.getPosbody(r)
		for p in posbody:
			ppred=self.getPred(p)	
			if ppred in self.domAbsPred:
				arglist=[k[3] for k in self.struct if k[0]==p]
				if arg in arglist:
					return [True,ppred]
				if "v"+arg in arglist:
					return [True,ppred]
		return [False]
	
	def checkFactHasAbs(self,p,index):
		#print "checking "+p+" for argument "+str(index)
		rulename=""
		for k in self.pred:
			if k[1]==p and "b" in k[0]:
				rulename=re.findall(r"(r\d+)[bh]",k[0])[0]
				break
		if rulename=="":
			#print "no rule uses this fact!"
			return [False]
		else:
			#print "rule "+rulename+" contains this pred"
			arg=self.getArgs(k[0])[index]
			ans=self.checkArgExistInAbsPred(rulename,arg)
			if True in ans:
			#	print "fact indeed has abs arg"
				return ans
			#print "fact does NOT have abs arg"
			return [False]

	def getDomAbsPredsInRule(self,r):
		return [p for p in self.getPosbody(r) if self.getPred(p) in self.domAbsPred]

	def checkIfPredHasNonDomAbsArg(self,checkp):
		rulename=re.findall(r"(r\d+)[bh]",checkp)[0]
		domabspredlist=self.getDomAbsPredsInRule(rulename)
		domabsargs=[k[3] for k in self.struct if k[0] in domabspredlist]
		mypredargs=[k[3] for k in self.struct if k[0]==checkp]
		for i in mypredargs:
			if i not in domabsargs:
				return True
		return False

	def checkIfRelatedWithAbsPred(self,r,checkp):
		global domabspred
		posbody=self.getPosbody(r)
		for p in posbody:
			ppred=self.getPred(p)	
			#if ppred in self.domAbsPred:
			if ppred==domabspred:
				ret=self.checkVarShare(checkp,p)
				if ret!=[]:
					#print p +" "+ checkp+" shares "+",".join(ret)
					return [True,ret]
		return [False]

	def ifHasConstantMakeAbstract(self,p,patom):
		const=[k[3] for k in self.struct if k[0]==p and k[2]=="const"]
		#print const
		if const!=[]:
			for m in self.mapping:
				if m[0]==const[0]:
					#TODO need an another additional check on whether the constant is indeed from the abs domain
					patomtemp=re.sub(r'([\,\(\=\<])'+const[0],r'\1'+m[1],patom)					
					#patom=patom.replace(const[0],m[1])
					if [patom,patomtemp] not in self.abstractedAtoms:
						self.abstractedAtoms.append([patom,patomtemp])
					return patomtemp
		return patom

	def checkIfInertia(self,r):
		#print r
		head=self.getHead(r)[0]
		#print head
		if head!=[]:
			headpred=self.getPred(head)
			#print headpred
			negbody=self.getNegbody(r)
			if len(negbody)==1:
				negpred=self.getPred(negbody[0])
				#print negpred
				if negpred=="neg"+headpred:
					#TODO need to further check whether they share the same arguments!!
					return True
		return False
						


	def hasConstant(self,p):
		const=[k[3] for k in self.struct if k[0]==p and k[2]=="const"]
		if const!=[]:
			return True
		return False
	
	def processFactsToAbstractFacts(self):
		absfactstext=""
		#print  self.absAtoms
		for a in self.absAtoms:
			if "_"+a[1] not in absfactstext:
				indeces=re.findall(r"X(([A-Z]*)\d+)",a[1])
				k=[]
				if indeces!=[]:
					abshead=a[1].replace("X","A")
					text=abshead+":-"+"_"+a[1]+","
					for i in indeces:
						k.append("mapTo("+i[1].lower()+", X"+str(i[0])+", A"+str(i[0])+")")
					k=", ".join(k)
					text=text+k+"."
				else:
					text=a[1]+":-"+"_"+a[1]+"."
				absfactstext=absfactstext+text+"\n"
		
		for a in self.factPreds:
			absfactstext=absfactstext+"_"+self.getAtom(a)[0]+".\n"##":- not check.\n"
		#print absfactstext
		#absfactstext=absfactstext+"less(A1,A2) :- X1<X2, mapTo(X1,A1), mapTo(X2,A2).\ngeq(A1,A2) :- X1>=X2, mapTo(X1,A1), mapTo(X2,A2).\n"
		#absfactstext=absfactstext+"plusOne(A,A1):- T1=T+1, mapTo(time,T,A), mapTo(time,T1,A1).\n"
		#absfactstext=absfactstext+"plusDistance(AT,AD,AE) :-  E=T+D, mapTo(times,T,AT), mapTo(times,D,AD), mapTo(times,E,AE).\n"
		fin=open("absrel_aux.txt","r")
		auxtext=fin.read()
		fin.close()
		absfactstext=absfactstext+auxtext
		text=""
		for a in self.atomList:
			if "neg" in a or "placeholder" in a: # or "aux_first" in a or "aux_second" in a:
				continue
			if "#show "+a not in text:
				arglength=len(a.split(","))
				atemp=a
				atemp=atemp.replace("choice_","")
				print atemp
				if "(" in atemp:
					text=text+"#show "+atemp[:atemp.index("(")]+"/"+str(arglength)+".\n"
				else:
					text=text+"#show "+atemp+".\n"
		absfactstext=absfactstext+text
		return absfactstext

	def checkCyclicDependencies(self):
		for a in self.rules:
			#FIXME for now assuming head has one atom!
			rule1head=self.getHead(a)[0]
			if rule1head==[]:
				continue
			rule1headpred=self.getPred(rule1head)
			for b in self.negbody:
				rule2negbodypred=self.getPred(b[1])
				if rule1headpred==rule2negbodypred:
					rule2head=self.getHead(b[0])[0]
					if rule2head==[]:
						continue
					rule2headpred=self.getPred(rule2head)
					if [rule1headpred,rule2headpred] in self.cyclicDep or [rule2headpred,rule1headpred] in self.cyclicDep:
						continue
					for c in self.negbody:
						rule3negbodypred2=self.getPred(c[1])							
						rule3head=self.getHead(c[0])[0]
						if rule3head==[]:
							continue
						if rule2headpred==rule3negbodypred2 and rule1headpred==self.getPred(rule3head):
							#print "cyclic dependency!! "+rule1headpred+" - "+rule2headpred
							self.cyclicDep.append([rule1headpred,rule2headpred])

def checkIfRelAndGetVars(m,p):
	return [[k[2],k[3]] for k in m.predRelVar if k[0]==p]


def checkIfRelAndGetVarsNonBin(m,p):
	gatherall1 = [[k[2],k[3],k[4],k[5]] for k in m.predRelVarNonBin if k[0]==p and len(k)==6]
	gatherall2 = [[k[2],k[3],k[4]] for k in m.predRelVarNonBin if k[0]==p and len(k)==5]
	return gatherall1 + gatherall2


def keepSameRule(m,r,relinfo,noabs):
	moretemp=[]
	#FIXME for now assuming head has one atom!
	h = m.getHead(r)[0]
	if h!=[]:
		head=m.getAtom(h)[0]
	else:
		head=""
	posbodytemp=m.getPosbody(r)
	ptext=[]
	for p in posbodytemp:
		ptemp=m.getAtom(p)[0]
		if relinfo!=[]:
			relvars=checkIfRelAndGetVars(m,p)
			if relvars==[]:
				relvars=checkIfRelAndGetVarsNonBin(m,p)
			if relvars!=[]:
				#FIXME ptemp should not containt any relation types
				if True in m.checkIfRelatedWithAbsPred(r,p) and m.hasConstant(p)==False:
					#for v in relvars[0]:
					#FIXME right now, only works for having one rel in rule, if has more than one rel, then puts same values to the arguments
					for i in range(0,len(relvars[0])):
						if re.match("[A-Z]",relvars[0][i])!=None:
							moretemp.append(relvars[0][i]+"="+relinfo[i+1])
		#deals with possibility of constants
		if noabs==False:
			ptemp=m.ifHasConstantMakeAbstract(p,ptemp)
		ptext.append(ptemp)
	negbodytemp=m.getNegbody(r)
	ptext=", ".join(ptext)
	ntext=[]
	for n in negbodytemp:
		ntemp=m.getAtom(n)[0]
		if noabs==False:
			ntemp=m.ifHasConstantMakeAbstract(n,ntemp)
		ntext.append("not "+ntemp)
	ntext=", ".join(ntext)
	if ptext!="":
		text=head+" :- "+ptext
		if ntext!="":
			text=text+", "+ntext+".\n"
		else:
			text=text+".\n"
	else:
		if ntext!="":
			text=head+" :- "+ntext+".\n"
		else:
			text=head+".\n"
	if moretemp!=[]:
		text=text.replace(".\n",", "+", ".join(moretemp)+".\n")
	return text

def keepSameRuleWithChoice(m,r,relinfo):
	#FIXME for now assuming head has one atom!
	h = m.getHead(r)[0]
	if h!=[]:
		moretemp=[]
		head="{"+m.getAtom(h)[0]+"}"
	#else:
	#	head=""
		posbodytemp=m.getPosbody(r)
		ptext=[]
		for p in posbodytemp:
			ptemp=m.getAtom(p)[0]
			if len(relinfo)>0 and relinfo[len(relinfo)-1]!="IV":
				relvars=checkIfRelAndGetVars(m,p)
				if relvars==[]:
					relvars=checkIfRelAndGetVarsNonBin(m,p)
				if relvars!=[]:
					#FIXME ptemp should not containt any relation types
					if True in m.checkIfRelatedWithAbsPred(r,p) and m.hasConstant(p)==False:									
						#for v in relvars[0]:
						for i in range(0,len(relvars[0])):
							if re.match("[A-Z]",relvars[0][i])!=None:
								moretemp.append(relvars[0][i]+"="+relinfo[i+1])
			ptemp=m.ifHasConstantMakeAbstract(p,ptemp)
			ptext.append(ptemp)
		negbodytemp=m.getNegbody(r)
		ptext=", ".join(ptext)
		ntext=[]
		for n in negbodytemp:
			ntemp=m.getAtom(n)[0]
			ntemp=m.ifHasConstantMakeAbstract(n,ntemp)
			ntext.append("not "+ntemp)
		ntext=", ".join(ntext)
		if ptext!="":
			text=head+" :- "+ptext
			if ntext!="":
				text=text+", "+ntext+".\n"
			else:
				text=text+".\n"
		else:
			if ntext!="":
				text=head+" :- "+ntext+".\n"
			else:
				text=head+".\n"
		if moretemp!=[]:
			text=text.replace(".\n",", "+", ".join(moretemp)+".\n")
	else: 
		#FIXME this gets rid of the constraints if they were decided to be changed to a choice rule
		text=""
	return text

def keepSameRuleWithChoiceAndShift(m,r,l,relinfo):
	#FIXME for now assuming head has one atom!
	h = m.getHead(r)[0]
	if h!=[]:
		moretemp=[]
		head="{"+m.getAtom(h)[0]+"}"
		posbodytemp=m.getPosbody(r)
		ptext=[]
		for p in posbodytemp:
			ptemp=m.getAtom(p)[0]
			#notice: here there is the check of IV
			if len(relinfo)>0 and relinfo[len(relinfo)-1]!="IV":
				relvars=checkIfRelAndGetVars(m,p)
				if relvars==[]:
					relvars=checkIfRelAndGetVarsNonBin(m,p)
				if relvars!=[]:
					#FIXME ptemp should not containt any relation types
					if True in m.checkIfRelatedWithAbsPred(r,p) and m.hasConstant(p)==False:					
						#for v in relvars[0]:
						for i in range(0,len(relvars[0])):
							if re.match("[A-Z]",relvars[0][i])!=None:
								moretemp.append(relvars[0][i]+"="+relinfo[i+1])
			ptemp=m.ifHasConstantMakeAbstract(p,ptemp)
			ptext.append(ptemp)
		negbodytemp=m.getNegbody(r)
		ptext=", ".join(ptext)
		ntext=[]
		removed=False
		for n in negbodytemp:
			#if n!=l:
			if n not in l:
				ntemp=m.getAtom(n)[0]
				ntemp=m.ifHasConstantMakeAbstract(n,ntemp)
				ntext.append("not "+ntemp)
			else:
				if isCyclicDependant(m,h,n)==False:
					ntemp=m.getAtom(n)[0]
					if relinfo==[]:
						if True in m.checkIfRelatedWithAbsPred(r,n) and m.hasConstant(n)==False:	
							clusters=m.getNonSingletonClusters()
							#print clusters
							[tr,varss]=m.checkIfRelatedWithAbsPred(r,n)
							#varss=[k[3] for k in m.struct if k[0]==n and k[2]=="var"]
							#print varss
							for c in clusters:
								for i in range(0,len(varss)):
									varss[i]=varss[i].replace("v","")
									if re.match("[A-Z]",varss[i])!=None:
										if varss[i]+"="+c not in moretemp:
											moretemp.append(varss[i]+"="+c)
							#print moretemp
					ntext.append(ntemp)	
				else:
					removed=True			
		ntext=", ".join(ntext)
		if ptext!="":
			text=head+" :- "+ptext
			if ntext!="":
				text=text+", "+ntext+".\n"
			else:
				text=text+".\n"
		else:
			if ntext!="":
				text=head+" :- "+ntext+".\n"
			else:
				text=head+".\n"
		if moretemp!=[]:
			if relinfo!=[]:
				text=text.replace(".\n",", "+", ".join(moretemp)+".\n")
			else:
				texttemp=""
				for k in moretemp:
					texttemp=texttemp+text.replace(".\n",", "+k+".\n")
				text=texttemp
		else:
			if relinfo==[] and removed==False:
				text=""
		
	else: 
		#this gets rid of the constraints if they were decided to be changed to a choice rule
		text=""
	return text


def keepSameRuleWithChoiceAndShiftAndRelShift(m,r,l,relinfo):
	#FIXME for now assuming head has one atom!
	h = m.getHead(r)[0]
	if h!=[]:
		moretemp=[]
		head="{"+m.getAtom(h)[0]+"}"
	#else:
	#	head=""
		posbodytemp=m.getPosbody(r)
		ptext=[]
		for p in posbodytemp:
			ptemp=m.getAtom(p)[0]
			relvars=checkIfRelAndGetVars(m,p)
			if relvars==[]:
				relvars=checkIfRelAndGetVarsNonBin(m,p)
			if relvars!=[]:
				#FIXME ptemp should not contain any relation types
				if True in m.checkIfRelatedWithAbsPred(r,p) and m.hasConstant(p)==False:
					#for v in relvars[0]:
					for i in range(0,len(relvars[0])):
						if re.match("[A-Z]",relvars[0][i])!=None:
							moretemp.append(relvars[0][i]+"="+relinfo[i+1])
			ptemptemp=m.ifHasConstantMakeAbstract(p,ptemp)
			if relinfo[0]=="neq":
				ptemptemp=ptemptemp.replace("!=","=")
				#ptemp=ptemp.replace("neq","equ")
			elif relinfo[0]=="less":
				ptemptemp=ptemptemp.replace("<",">=")
				#ptemp=ptemp.replace("less","geq")
			elif relinfo[0]=="greater":
				ptemptemp=ptemptemp.replace(">","<=")
			elif relinfo[0]=="geq":
				ptemptemp=ptemptemp.replace(">=","<")
				#ptemp=ptemp.replace("geq","less")
			elif relinfo[0]=="leq":
				ptemptemp=ptemptemp.replace("<=",">")
			elif relinfo[0]=="plus":
				ptemptemp=ptemptemp.replace("=","!=")
			elif relinfo[0]=="neqEqu":
				ptemptemp=ptemptemp.replace("neqEqu","neg_neqEqu")
			elif relinfo[0]=="neqNeq":
				ptemptemp=ptemptemp.replace("neqNeq","neg_neqNeq")
			elif relinfo[0]=="equEqu":
				ptemptemp=ptemptemp.replace("equEqu","neg_equEqu")
			elif relinfo[0]=="leqLeq":
				ptemptemp=ptemptemp.replace("leqLeq","neg_leqLeq")
			elif relinfo[0]=="leqEqu":
				ptemptemp=ptemptemp.replace("leqEqu","neg_leqEqu")
			elif relinfo[0]=="leqLess":
				ptemptemp=ptemptemp.replace("leqLess","neg_leqLess")
			elif relinfo[0]=="lessLess":
				ptemptemp=ptemptemp.replace("lessLess","neg_lessLess")
			else:
				print "unfamiliar rel type!!!!"
				sys.exit()
			if ptemp!=ptemptemp:
				if [ptemp,ptemptemp] not in m.abstractedAtoms:
					m.abstractedAtoms.append([ptemp,ptemptemp])
			ptemp=ptemptemp
			ptext.append(ptemp)
		negbodytemp=m.getNegbody(r)
		ptext=", ".join(ptext)
		ntext=[]
		for n in negbodytemp:
			#if n!=l:
			if n not in l:
				ntemp=m.getAtom(n)[0]
				ntemp=m.ifHasConstantMakeAbstract(n,ntemp)
				ntext.append("not "+ntemp)
			else:
				if isCyclicDependant(m,h,n)==False:
					ntemp=m.getAtom(n)[0]
					ntext.append(ntemp)				
		ntext=", ".join(ntext)
		if ptext!="":
			text=head+" :- "+ptext
			if ntext!="":
				text=text+", "+ntext+".\n"
			else:
				text=text+".\n"
		else:
			if ntext!="":
				text=head+" :- "+ntext+".\n"
			else:
				text=head+".\n"
		if moretemp!=[]:
			text=text.replace(".\n",", "+", ".join(moretemp)+".\n")
	else: 
		#this gets rid of the constraints if they were decided to be changed to a choice rule
		text=""
	return text

def isCyclicDependant(m,p1,p2):
	pred1=m.getPred(p1)
	pred2=m.getPred(p2)
	if [pred1,pred2] in m.cyclicDep or [pred2,pred1] in m.cyclicDep:
		return True
	return False
	
def constructAbsRules(m,reltypetrue,reltypefalse):
	absrules=""
	for r in m.rules:
		if r in m.facts:
			#print "rule "+r+" is a fact - moving on"
			continue
		#TODO inertia check should be removed when abstracting over time... right?
		#if m.checkIfInertia(r)==True:
		#	absrules=absrules+"%rule "+r+": inertia rule - keepSameRule\n"
		#	absrules=absrules+keepSameRule(m,r,[],True)
		#	continue			
		#rulerelinfo=m.ruleRel[m.rules.index(r)]
		allrulerels=[k for k in m.ruleRel if k[0]==r]
		#print allrulerels
		rulesNegBody=m.getNegbody(r)
		for rulerelinfo in allrulerels:
			rulerel=rulerelinfo[2]
			if rulesNegBody==[]:
				if rulerel=="none":
					absrules=absrules+"%rule "+r+": norel + no negbody - keepSameRule\n"
					absrules=absrules+keepSameRule(m,r,[],False)
				else:
					relabsshare=m.checkIfRelatedWithAbsPred(r,rulerelinfo[1])
					if False in relabsshare:
						#print "rule "+r+": rel "+rulerelinfo[1]+" does not share variables with abstracted domain"
						hasAnotherUsedRel=False
						for i in allrulerels:
							if True in m.checkIfRelatedWithAbsPred(r,i[1]):
								hasAnotherUsedRel=True
								break
						if hasAnotherUsedRel==False:
							absrules=absrules+"%rule "+r+": not sharing var with abs dom - keepSameRule\n"
							absrules=absrules+keepSameRule(m,r,[],True)
						else:
							absrules=absrules+"%rule "+r+": not sharing var with abs dom + but has another used rel - do nothing\n"
						continue
					relinfotrue=[k for k in reltypetrue if k[0]==rulerel and m.checkRelatedWithRuleRel(k,rulerelinfo[1])]
					relinfofalse=[k for k in reltypefalse if k[0]==rulerel and m.checkRelatedWithRuleRel(k,rulerelinfo[1])]
					for k in relinfotrue:
						if k[len(k)-1]=="III":
							absrules=absrules+"%rule "+r+": splus + no negbody - keepSameRuleWithChoice\n"
							absrules=absrules+"%"+",".join(k)+"\n"
							absrules=absrules+keepSameRuleWithChoice(m,r,k)
						if k[len(k)-1]=="I":
							absrules=absrules+"%rule "+r+": splus + no negbody - keepSameRule\n"
							absrules=absrules+"%"+",".join(k)+"\n"
							absrules=absrules+keepSameRule(m,r,k,False)				
					for k in relinfofalse:
						#FIXME neq a1,a1 is not related with L!=1 which gets rel shift to L=a0.
						#rule r20: splus + no negbody - keepSameRuleWithChoiceAndRelShift
						#%neq,a1,a1,IV
						#{somethingOnTheRest(T)} :- onTable(B,L,T), block(B), table(L), L=a0.
						if k[len(k)-1]=="IV":
							absrules=absrules+"%rule "+r+": splus + no negbody - keepSameRuleWithChoiceAndRelShift\n"
							absrules=absrules+"%"+",".join(k)+"\n"
							absrules=absrules+keepSameRuleWithChoiceAndShiftAndRelShift(m,r,"",k)
						if k[len(k)-1]=="V":
							absrules=absrules+"%rule "+r+": splus + no negbody - keepSameRuleWithChoice\n"
							absrules=absrules+"%"+",".join(k)+"\n"
							absrules=absrules+keepSameRuleWithChoice(m,r,k)
			else:
				rulesPosBody=[l for l in m.getPosbody(r) if m.getPred(l) not in m.specialPreds]
				if rulesPosBody==[]:
					if rulerel=="none":
						absrules=absrules+"%rule "+r+": norel + no posbody - keepSameRule\n"
						absrules=absrules+keepSameRule(m,r,[],False)				
						for s in rulesNegBody:
							sabsshare=m.checkIfRelatedWithAbsPred(r,s)
							if False in sabsshare:
								print "rule "+r+": "+s+" does not share variables with abstracted domain - not shifting"
								continue
							#this shifts for all neg's with cluster mappings
							absrules=absrules+"%rule "+r+": norel + no posbody - keepSameRuleWithChoiceAndShift "+s+"\n"
							absrules=absrules+keepSameRuleWithChoiceAndShift(m,r,s,[])
					else:
						relabsshare=m.checkIfRelatedWithAbsPred(r,rulerelinfo[1])
						if False in relabsshare:
							#print "rule "+r+": rel "+rulerelinfo[1]+" does not share variables with abstracted domain"
							hasAnotherUsedRel=False
							for i in allrulerels:
								if True in m.checkIfRelatedWithAbsPred(r,i[1]):
									hasAnotherUsedRel=True
									break
							if hasAnotherUsedRel==False:
								absrules=absrules+"%rule "+r+": not sharing var with abs dom - keepSameRule\n"
								absrules=absrules+keepSameRule(m,r,[],True)
							else:
								absrules=absrules+"%rule "+r+": not sharing var with abs dom + but has another used rel - do nothing\n"
							continue
						sminus=m.getSminus(r)
						sminus=list(set(sminus))
						relinfotrue=[k for k in reltypetrue if k[0]==rulerel and m.checkRelatedWithRuleRel(k,rulerelinfo[1])]
						relinfofalse=[k for k in reltypefalse if k[0]==rulerel and m.checkRelatedWithRuleRel(k,rulerelinfo[1])]
						#for s in sminus:
						for i in xrange(1,len(sminus)+1):
							listing = [list(x) for x in itertools.combinations(sminus, i)]
							for s in listing:							
								for k in relinfotrue:
									if k[len(k)-1]=="III":
										absrules=absrules+"%rule "+r+": sminus + no posbody - keepSameRuleWithChoiceAndShift "+",".join(s)+"\n"
										absrules=absrules+"%"+",".join(k)+"\n"
										absrules=absrules+keepSameRuleWithChoiceAndShift(m,r,s,k)
									if k[len(k)-1]=="I":
										absrules=absrules+"%rule "+r+": sminus + no posbody - keepSameRule\n"
										absrules=absrules+"%"+",".join(k)+"\n"
										absrules=absrules+keepSameRule(m,r,k,False)	
								for k in relinfofalse:
									if k[len(k)-1]=="IV":
										absrules=absrules+"%rule "+r+": sminus + no posbody - keepSameRuleWithChoiceAndRelShift\n"
										absrules=absrules+"%"+",".join(k)+"\n"
										absrules=absrules+keepSameRuleWithChoiceAndShiftAndRelShift(m,r,"",k)
										absrules=absrules+"%rule "+r+": sminus + no posbody - keepSameRuleWithChoiceAndShiftAndRelShift "+",".join(s)+"\n"
										absrules=absrules+"%"+",".join(k)+"\n"
										absrules=absrules+keepSameRuleWithChoiceAndShiftAndRelShift(m,r,s,k)
										absrules=absrules+"%rule "+r+": sminus + no posbody - keepSameRuleWithChoiceAndShift "+",".join(s)+"\n"
										absrules=absrules+"%"+",".join(k)+"\n"
										absrules=absrules+keepSameRuleWithChoiceAndShift(m,r,s,k)
									if k[len(k)-1]=="V":
										absrules=absrules+"%rule "+r+": sminus + no posbody - keepSameRuleWithChoiceAndShift "+",".join(s)+"\n"
										absrules=absrules+"%"+",".join(k)+"\n"
										absrules=absrules+keepSameRuleWithChoiceAndShift(m,r,s,k)
				else:
					if rulerel=="none":
						#keep same rule
						absrules=absrules+"%rule "+r+": norel - keepSameRule\n"
						absrules=absrules+keepSameRule(m,r,[],False)
						for s in rulesNegBody:
							sabsshare=m.checkIfRelatedWithAbsPred(r,s)
							if False in sabsshare:
								print "rule "+r+": "+s+" does not share variables with abstracted domain - not shifting"
								continue
							#this shifts for all neg's with cluster mappings
							absrules=absrules+"%rule "+r+": sminus + norel - keepSameRuleWithChoiceAndShift "+s+"\n"
							absrules=absrules+keepSameRuleWithChoiceAndShift(m,r,s,[])
					else:
						relabsshare=m.checkIfRelatedWithAbsPred(r,rulerelinfo[1])
						if False in relabsshare:
							#print "rule "+r+": rel "+rulerelinfo[1]+" does not share variables with abstracted domain"
							hasAnotherUsedRel=False
							for i in allrulerels:
								if True in m.checkIfRelatedWithAbsPred(r,i[1]):
									hasAnotherUsedRel=True
									break
							if hasAnotherUsedRel==False:
								absrules=absrules+"%rule "+r+": not sharing var with abs dom - keepSameRule\n"
								absrules=absrules+keepSameRule(m,r,[],True)
							else:
								absrules=absrules+"%rule "+r+": not sharing var with abs dom + but has another used rel - do nothing\n"
							continue
						relinfotrue=[k for k in reltypetrue if k[0]==rulerel and m.checkRelatedWithRuleRel(k,rulerelinfo[1])]
						relinfofalse=[k for k in reltypefalse if k[0]==rulerel and m.checkRelatedWithRuleRel(k,rulerelinfo[1])]
						splus=m.getSplus(r)
						splus=list(set(splus))
						sminus=m.getSminus(r)
						sminus=list(set(sminus))
						if splus!=[]:
							for k in relinfotrue:
								if k[len(k)-1]=="III":
									absrules=absrules+"%rule "+r+": splus - keepSameRuleWithChoice\n"
									absrules=absrules+"%"+",".join(k)+"\n"
									absrules=absrules+keepSameRuleWithChoice(m,r,k)
								if k[len(k)-1]=="I":
									absrules=absrules+"%rule "+r+": splus - keepSameRule\n"
									absrules=absrules+"%"+",".join(k)+"\n"
									absrules=absrules+keepSameRule(m,r,k,False)				
							for k in relinfofalse:
								if k[len(k)-1]=="IV":
									absrules=absrules+"%rule "+r+": splus - keepSameRuleWithChoiceAndRelShift\n"
									absrules=absrules+"%"+",".join(k)+"\n"
									absrules=absrules+keepSameRuleWithChoiceAndShiftAndRelShift(m,r,"",k)
								if k[len(k)-1]=="V":
									absrules=absrules+"%rule "+r+": splus - keepSameRuleWithChoice\n"
									absrules=absrules+"%"+",".join(k)+"\n"
									absrules=absrules+keepSameRuleWithChoice(m,r,k)
						keptsamerulesminus=False
						#for s in sminus:
						for i in xrange(1,len(sminus)+1):
							listing = [list(x) for x in itertools.combinations(sminus, i)]
							for s in listing:
								#TODO check this step of the process, should the rule be kept the same even if splus!=[] and some process was done on the rule already?
								if splus==[] and not keptsamerulesminus:
									absrules=absrules+"%rule "+r+": sminus + no splus - keepSameRule\n"
									absrules=absrules+keepSameRule(m,r,[],False)
									keptsamerulesminus=True
									#TODO add additional choice rules for the atoms in "not a(X)"
								for k in relinfotrue:
									if k[len(k)-1]=="III":
										absrules=absrules+"%rule "+r+": sminus - keepSameRuleWithChoiceAndShift "+",".join(s)+"\n"
										absrules=absrules+"%"+",".join(k)+"\n"
										absrules=absrules+keepSameRuleWithChoiceAndShift(m,r,s,k)				
								for k in relinfofalse:
									if k[len(k)-1]=="IV":
										if splus==[]:
											absrules=absrules+"%rule "+r+": sminus - keepSameRuleWithChoiceAndRelShift\n"
											absrules=absrules+"%"+",".join(k)+"\n"
											absrules=absrules+keepSameRuleWithChoiceAndShiftAndRelShift(m,r,"",k)
										absrules=absrules+"%rule "+r+": sminus - keepSameRuleWithChoiceAndShiftAndRelShift "+",".join(s)+"\n"
										absrules=absrules+"%"+",".join(k)+"\n"
										absrules=absrules+keepSameRuleWithChoiceAndShiftAndRelShift(m,r,s,k)
										absrules=absrules+"%rule "+r+": sminus - keepSameRuleWithChoiceAndShift "+",".join(s)+"\n"
										absrules=absrules+"%"+",".join(k)+"\n"
										absrules=absrules+keepSameRuleWithChoiceAndShift(m,r,s,k)
									if k[len(k)-1]=="V":
										absrules=absrules+"%rule "+r+": sminus - keepSameRuleWithChoiceAndShift "+",".join(s)+"\n"
										absrules=absrules+"%"+",".join(k)+"\n"
										absrules=absrules+keepSameRuleWithChoiceAndShift(m,r,s,k)
						if sminus==[]:
							for s in rulesNegBody:
								sabsshare=m.checkIfRelatedWithAbsPred(r,s)
								if False in sabsshare:
									print "rule "+r+": "+s+" does not share variables with abstracted domain - not shifting"
									continue
								#this shifts for all neg's with cluster mappings
								absrules=absrules+"%rule "+r+": no sminus - keepSameRuleWithChoiceAndShift "+s+"\n"
								absrules=absrules+keepSameRuleWithChoiceAndShift(m,r,s,[])
						

						
	#print absrules
	return absrules

def preProcessRangeAndTimeAndChoice(text):
	#FIXME what if there is a(1..n) ?
	#FIXME or what if there is a(1..3,red).?
	dots=re.findall(r"(\w+)\((\d+)\.\.(\d+)\).",text)
	changed=False
	for a in dots:
		text=text.replace(a[0]+"("+a[1]+".."+a[2]+").", "")
		for i in range(int(a[1]),int(a[2])+1):
			text=text+a[0]+"("+str(i)+")."
		text=text+"\n"
		changed=True
	#print text
	textchoices=re.findall(r"(%*(\d*)\{(.*)\}(\d*)(.*:-.*.))",text)
	#print textchoices
	textkeepchoices=[]
	if textchoices!=[]:
		gatherchoicestemp=[k for k in textchoices if k[0][0]!="%" and k[1]!='' and ":" in k[2] or ";" in k[2]]
		textkeepchoices=[k for k in textchoices if k[0][0]!="%" and k[1]=='' and k[3]=='' and ":" not in k[2] and ";" not in k[2]]
		textchoices=list(set(gatherchoicestemp))
	#print textchoicestemp
	#print textkeepchoices
	
	texttemp=re.sub(r'(\d*\{.*\}\d*.*:-.*.)', r'',text)
	texttemp=re.sub(r'T\-1',r'TMINUS1',texttemp)
	texttemp=re.sub(r'T\+1',r'TPLUS1',texttemp)

	for k in textkeepchoices:
		texttemp=texttemp+"\nchoice_"+k[2]+k[4]+"\n"
	if textkeepchoices!=[] and textchoices==[]:
		textchoices=["-"]
	elif textchoices!=[]:
		for a in range(0,len(textchoices)):
			texttemp=texttemp+"choice_placeholder_"+str(a)+textchoices[a][4]+"\n"
	if texttemp!=text:
		changed=True
	text=texttemp
	text=re.sub(r'(#show .*)', r'%\1',text)
	return [text,changed,textchoices]

def postProcessChoice(text,textchoices,abstractedAtoms):
	if textchoices!=["-"]:
		for a in range(0,len(textchoices)):
			#FIXME right now replaces all the placeholders with the original choice head - no limit is changed
			text=re.sub(r'\{choice_placeholder_'+str(a)+'\}(.*:-.*.)', textchoices[a][1]+'{'+textchoices[a][2]+'}'+textchoices[a][3]+r'\1',text)
			text=re.sub(r'choice_placeholder_'+str(a)+'( :-.*.)', textchoices[a][1]+'{'+textchoices[a][2]+'}'+textchoices[a][3]+r'\1',text)
	text=re.sub(r'\{choice\_(.*)\}(.*:-.*.)', r'{\1}\2',text)
	text=re.sub(r'choice\_(.*)(.*:-.*.)', r'{\1}\2',text)
	return text

def createAbsCheckRules(atomlist,interestedelts):
	text=""
	for a in atomlist:
		if "neg" in a  or "placeholder" in a:# or "aux_second" in a or "aux_first" in a:
			continue
		if "("+a not in text:
			indeces=re.findall(r"X(([A-Z]*)\d+)",a)
			k=[]
			kk=[]
			a=a.replace("TPLUS1","T+1")
			a=a.replace("TMINUS1","T-1")
			a=a.replace("choice_","")
			if indeces!=[]:
				for i in indeces:
					k.append("mapTo("+i[1].lower()+", X"+str(i[0])+", A"+str(i[0])+")")
					kk.append("care(A"+str(i[0])+")")
				k=", ".join(k)
				kk=", ".join(kk)
				if interestedelts!=[]:
					text=text+":- not absexists("+a.replace("X","A")+"), "+a+", "+k+", "+kk+".\n"
					text=text+":- absexists("+a.replace("X","A")+"), {"+a+": "+k+"}0, "+kk+".\n"
				else:
					text=text+":- not absexists("+a.replace("X","A")+"), "+a+", "+k+".\n"
					text=text+":- absexists("+a.replace("X","A")+"), {"+a+": "+k+"}0.\n"
			else:
				text=text+":- not absexists("+a+"), "+a+".\n"
				text=text+":- absexists("+a+"), {"+a+"}0.\n"

	if interestedelts!=[]:
		for i in interestedelts:
			text=text+"_care("+str(i)+").\n"
		text=text+"care(A) :- _care(X), mapTo(_,X,A).\n"
				
	return text

def getUsedRelsAbsTypes(specialPred,textOrg):
	textOrg=re.sub(r'\%.*', r'',textOrg)
	reltypetrue=[]
	reltypefalse=[]
	absInfo=[]
	auxtext=""
	auxnonbinreltext=""
	for rel in specialPred:
		if rel in ["equ","neq","less","greater","geq","leq"]:
			if rel=="equ":
				sign="="
			elif rel=="neq":
				sign="!="
			elif rel=="less":
				sign="<"
			elif rel=="greater":
				sign=">"
			elif rel=="geq":
				sign=">="
			elif rel=="leq":
				sign="<="
			if re.search(sign+r'[^=]',textOrg):
				#call computeRelType.lp with mapping.lp to get output reltype.txt 
				#FIXME can avoid writing on a file, and just use the output
				fout = open("reltype.txt","w")
				p = pexpect.spawn("clingo reltype_computation/computeRelType_"+rel+"_lifted.lp "+mapping,timeout=600)
				p.logfile=fout
				a=p.expect([pexpect.EOF,'ERROR',pexpect.TIMEOUT])
				fout.close()
				if a == 1 or a==2: # Timeout
					print "Timeout or Error"
					sys.exit()
				fin=open("reltype.txt","r")
				textrel=fin.read()
				fin.close()
				relI=re.findall(r"rel\("+domabspred+",(\S+),(\S+),(\S+),(\S+)\)",textrel)
				for rel in relI:
					if rel[len(rel)-1]=="i":
						reltypetrue.append([rel[0],rel[1],rel[2],"I"])
					elif rel[len(rel)-1]=="iii":
						reltypetrue.append([rel[0],rel[1],rel[2],"III"])
					elif rel[len(rel)-1]=="ii":
						reltypefalse.append([rel[0],rel[1],rel[2],"II"])
					else:
						reltypefalse.append([rel[0],rel[1],rel[2],"IV"])
				if absInfo==[]:
					cluster=re.findall(r"isCluster\("+domabspred+",(\S+)\)",textrel)
					unique=re.findall(r"isUnique\("+domabspred+",(\S+)\)",textrel)
					mappiing=re.findall(r"mapTo\("+domabspred+",(\S+),\ *(\S+)\)",textrel)
					absInfo=[mappiing, cluster , unique]	
		else:
			if rel=="plus":
				continue
			if re.search(rel,textOrg):
				args3=False
				args4=False
				if re.search(rel+"\(\w+,\w+,\w+\)",textOrg):
					args3=True
				if re.search(rel+"\(\w+,\w+,\w+,\w+\)",textOrg):
					args4=True
				if args3==False and args4==False:
					print "args num not defined yet!"
					sys.exit()
				
				if args3==True:
					fout = open("reltype_nonbin.txt","w")
					p = pexpect.spawn("clingo reltype_computation/computeRelType_relcombination_"+rel+"3_lifted.lp "+mapping,timeout=600)
					p.logfile=fout
					a=p.expect([pexpect.EOF,'ERROR',pexpect.TIMEOUT])
					fout.close()
					if a == 1 or a==2: # Timeout
						print "Timeout or Error"
						sys.exit()
					fin=open("reltype_nonbin.txt","r")
					textrel=fin.read()
					fin.close()
					relI=re.findall(r"rel\("+domabspred+",(\w+),(\w+),(\w+),(\w+),(\w+)\)",textrel)
					for reel in relI:
						if reel[4]=="i":
							reltypetrue.append([reel[0],reel[1],reel[2],reel[3],"I"])
						elif reel[4]=="ii":
							reltypefalse.append([reel[0],reel[1],reel[2],reel[3],"II"])
						elif reel[4]=="iii":
							reltypetrue.append([reel[0],reel[1],reel[2],reel[3],"III"])
						else:
							reltypefalse.append([reel[0],reel[1],reel[2],reel[3],"IV"])	
					if rel=="equEqu":
						auxtext=auxtext+"equEqu(A1,A2,A3) :- A1=A2,A2=A3, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\nneg_equEqu(A1,A2,A3) :- A1!=A2, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\nneg_equEqu(A1,A2,A3) :- A2!=A3, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\n"
						auxnonbinreltext=auxnonbinreltext+"equEqu(X1,X2,X3) :- X1=X2,X2=X3, dom(X1), dom(X2), dom(X3).\n"
					elif rel=="neqEqu":
						auxtext=auxtext+"neqEqu(A1,A2,A3) :- A1!=A2,A2=A3, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\nneg_neqEqu(A1,A2,A3) :- A1=A2, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\nneg_neqEqu(A1,A2,A3) :- A2!=A3, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\n"
						auxnonbinreltext=auxnonbinreltext+"neqEqu(X1,X2,X3) :- X1!=X2,X2=X3, dom(X1), dom(X2), dom(X3).\n"
					elif rel=="neqNeq":
						auxtext=auxtext+"neqNeq(A1,A2,A3) :- A1!=A2,A2!=A3, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\nneg_neqNeq(A1,A2,A3) :- A1=A2,mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\nneg_neqNeq(A1,A2,A3) :- A2=A3,mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\n"
						auxnonbinreltext=auxnonbinreltext+"neqNeq(X1,X2,X3) :- X1!=X2,X2!=X3, dom(X1), dom(X2), dom(X3).\n"
					elif rel=="leqLess":
						auxtext=auxtext+"leqLess(A1,A2,A3) :- A1<=A2,A2<A3, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\nneg_leqLess(A1,A2,A3) :- A1>A2,mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\nneg_leqLess(A1,A2,A3) :- A2>=A3,mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\n"
						auxnonbinreltext=auxnonbinreltext+"leqLess(X1,X2,X3) :- X1<=X2,X2<X3, dom(X1), dom(X2), dom(X3).\n"
					elif rel=="lessLess":
						auxtext=auxtext+"lessLess(A1,A2,A3) :- A1<A2,A2<A3, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\nneg_lessLess(A1,A2,A3) :- A1>=A2,mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\nneg_lessLess(A1,A2,A3) :- A2>=A3,mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3).\n"
						auxnonbinreltext=auxnonbinreltext+"lessLess(X1,X2,X3) :- X1<X2,X2<X3, dom(X1), dom(X2), dom(X3).\n"
					else:
						print rel + "rel not considered for arg 3 yet!"
						sys.exit()
				if args4==True:					
					fout = open("reltype_nonbin.txt","w")
					p = pexpect.spawn("clingo reltype_computation/computeRelType_relcombination_"+rel+"4_lifted.lp "+mapping,timeout=600)
					p.logfile=fout
					a=p.expect([pexpect.EOF,'ERROR',pexpect.TIMEOUT])
					fout.close()
					if a == 1 or a==2: # Timeout
						print "Timeout or Error"
						sys.exit()
					fin=open("reltype_nonbin.txt","r")
					textrel=fin.read()
					fin.close()
					relI=re.findall(r"rel\("+domabspred+",(\w+),(\w+),(\w+),(\w+),(\w+),(\w+)\)",textrel)
					for reel in relI:
						if reel[5]=="i":
							reltypetrue.append([reel[0],reel[1],reel[2],reel[3],reel[4],"I"])
						elif reel[5]=="ii":
							reltypefalse.append([reel[0],reel[1],reel[2],reel[3],reel[4],"II"])
						elif reel[5]=="iii":
							reltypetrue.append([reel[0],reel[1],reel[2],reel[3],reel[4],"III"])
						else:
							reltypefalse.append([reel[0],reel[1],reel[2],reel[3],reel[4],"IV"])
					if rel=="equEqu":
						auxtext=auxtext+"equEqu(A1,A2,A3,A4) :- A1=A2,A3=A4, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).\nneg_equEqu(A1,A2,A3,A4) :- A1!=A2, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).\nneg_equEqu(A1,A2,A3,A4) :- A3!=A4, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).\n"
						auxnonbinreltext=auxnonbinreltext+"equEqu(X1,X2,X3,X4) :- X1=X2,X3=X4, dom(X1), dom(X2), dom(X3), dom(X4).\n"
					elif rel=="neqEqu":
						auxtext=auxtext+"neqEqu(A1,A2,A3,A4) :- A1!=A2,A3=A4, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).\nneg_neqEqu(A1,A2,A3,A4) :- A1=A2, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).\nneg_neqEqu(A1,A2,A3,A4) :- A3!=A4, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).\n"
						auxnonbinreltext=auxnonbinreltext+"neqEqu(X1,X2,X3,X4) :- X1!=X2,X3=X4, dom(X1), dom(X2), dom(X3), dom(X4).\n"
					elif rel=="leqEqu":
						auxtext=auxtext+"leqEqu(A1,A2,A3,A4) :- A1<=A2,A3=A4, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).\nneg_leqEqu(A1,A2,A3,A4) :- A1>A2, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).\nneg_leqEqu(A1,A2,A3,A4) :- A3!=A4, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).\n"
						auxnonbinreltext=auxnonbinreltext+"leqEqu(X1,X2,X3,X4) :- X1<=X2,X3=X4, dom(X1), dom(X2), dom(X3), dom(X4).\n"
					elif rel=="leqLeq":
						auxtext=auxtext+"leqLeq(A1,A2,A3,A4) :- A1<=A2,A3<=A4, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).\nneg_leqLeq(A1,A2,A3,A4) :- A1>A2, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).\nneg_leqLeq(A1,A2,A3,A4) :- A3>A4, mapTo(ABS,X1,A1), mapTo(ABS,X2,A2), mapTo(ABS,X3,A3), mapTo(ABS,X4,A4).\n"
						auxnonbinreltext=auxnonbinreltext+"leqLeq(X1,X2,X3,X4) :- X1<=X2,X3<=X4, dom(X1), dom(X2), dom(X3), dom(X4).\n"
					else:
						print rel + "rel not considered for arg 4 yet!"
						sys.exit()

		

		
	auxnonbinreltext=auxnonbinreltext+"dom(X) :- "+domabspred+"(X).\n"
	fout=open("absrel_aux.txt","w")
	fout.write(auxtext)
	fout.close()
	fout=open("aux_nonbinaryrelations.lp","w")
	fout.write(auxnonbinreltext)
	fout.close()
	#print reltypetrue
	#print reltypefalse
	return [reltypetrue,reltypefalse,absInfo]
	

#input needs to be the MetaTranslator output of the program
fileorg=sys.argv[1]
mapping=sys.argv[2]
#get as input the atom that dom abs is being done, then add this to specialPred
domabspredicates=sys.argv[3]
domabspredicates=domabspredicates.split(",")

interestedelts=[]

if len(sys.argv) ==5:
	interestedelts=sys.argv[4]
	interestedelts=interestedelts.split(",")
	

	


fin=open(fileorg,"r")
textOrg=fin.read()
fin.close()


domAbsPreds=domabspredicates
print domAbsPreds

firsttime=True
for domabspred in domabspredicates:
	
	fileorg=fileorg.replace("meta","next")

	specialPred=["equ","neq","less","greater","geq","leq","plus","equEqu","neqEqu","neqNeq","leqLeq","leqLess","lessLess","leqEqu"]

	[reltypetrue,reltypefalse,absInfo]=getUsedRelsAbsTypes(specialPred,textOrg)

	specialPred.append(domabspred)

	#check if input is metatranslator output
	if "#maxint" not in textOrg:
		[textNew,changed,textchoices]=preProcessRangeAndTimeAndChoice(textOrg)
		if changed==True:
			fileorg=fileorg+"_input"
			fout=open(fileorg,"w")
			fout.write(textNew)
			fout.close()
		if "{}" not in textOrg:
			os.system("java -jar MetaTranslator.jar "+fileorg+" aux_curlybrackets.lp > "+fileorg+"_meta")
		else:
			os.system("java -jar MetaTranslator.jar "+fileorg+" > "+fileorg+"_meta")
		#if not, translate it to the meta form
		fileorg=fileorg+"_meta"
		fin=open(fileorg,"r")
		textOrg=fin.read()
		fin.close()		

	




	m=meta(textOrg,specialPred,domAbsPreds, absInfo)
	m.initializeAtoms()
	m.printout()


	m.checkCyclicDependencies()

	
	if firsttime==True:

		#TODO right now does the conversion at each call, but if just the mapping is refined, no need to recreate this conversion.
		absfactconversiontext = m.processFactsToAbstractFacts()
		fileorgabs=fileorg.replace("meta","absfacts")
		fout=open(fileorgabs,"w")
		fout.write(absfactconversiontext)
		fout.close()

		checkrules=createAbsCheckRules(m.atomList,interestedelts)
		fileorgcheck=fileorg.replace("meta","checkrules")
		fout=open(fileorgcheck,"w")
		fout.write(checkrules)
		fout.close()
		firsttime=False


	print "----Starting Construction----"
	absrules=constructAbsRules(m,reltypetrue,reltypefalse)
	name=fileorg.replace("meta","abs")
	fout=open(name,"w")
	if textchoices!=[]:
		#fout2=open("debugging_"+domabspred+".txt","w")
		#fout2.write(absrules)
		#fout2.close()
		print m.abstractedAtoms		
		absrules=postProcessChoice(absrules,textchoices, m.abstractedAtoms)
		#fout2=open("debugging_afterpostprocess_"+domabspred+".txt","w")
		#fout2.write(absrules)
		#fout2.close()
	fout.write(absrules)
	fout.close()

	textOrg=absrules



