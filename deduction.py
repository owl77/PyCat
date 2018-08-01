print 
print "Welcome to CatLog v0.1"
print
print "type help() for command list"
print

def help():
 print "Obj(<name>) - creates an object"
 print "Comp(<name1>,<name2>) - composes two arrows"
 print "Conj(<name1>,<name2>) - creates conjunction object with associated morphisms"
 print "Join(<name1>,<name2>) - <f,g> - see Lambek and Scott p.48"
 print "Imp(<name1>,<name2>) -  internal implication <name1> <= <name2>"
 print "Trans(<name>) - transpose f* - see Lambek and Scott p.49"
 print "Hyp(<arrowname>,<source>,<target>) - introduces a hypothesis (creates an arrow)"
 print "disp() - displays current objects, arrows and history"
 print "equations() - displays category equations (Work in Progress)"
 print "Sym(n) - adds B = A if A = B is equation n"
 print "Tr(n,m) - adds A = C if equation n is A = B and equation m is B = C"
 print "Sub(n,m,t) - (Work in Progress)"
 print "clear() - clear current environment"
 return


Equations = []
Objects = []
Arrows = []

IEquations = []
IObjects = []
IArrows = []
IUni = []
eqnum = 0

Rules = []

init = 0

def clear():
 global Equations 
 global Objects 
 global Arrows 

 global IEquations 
 global IObjects 
 global IArrows 
 global IUni 
 global Rules 
 global init 

 Equations = []
 Objects = []
 Arrows = []
 IEquations = []
 IObjects = []
 IArrows = []
 IUni = []
 Rules = []
 init = 0
 


 Object("T")


def parse1(s):
 if len(s) == 1:
  return True
 val =[n for n in range(len(s)) if (s == s[0:n] + " /\ " + s[n+4:] and parse1(s[1:n-1]) and parse1(s[n+4:len(s)-1])) or (s == s[0:n] + " <= " + s[n+4:] and parse1(s[1:n-1]) and parse1(s[n+4:len(s)-1]))]                                          
 if val!=[]:
  return True
 return False



def parse(o, s):
 val =[n for n in range(len(s)) if s == s[0:n] + o + s[n+len(o):] and parse1(s[1:n-1]) and parse1(s[n+len(o):len(s)-1])]
 if val !=[] :
  n = val[0]
  return [s[1:n],s[n+len(o):len(s)-1]]
 else:
  return []

class Arrow:
 def __init__(self,name, source, target):
  global Arrows 
  global eqnum
  self.name = name
  self.source = source
  self.target = target
  Arrows.append(self.display())
  print("added: "+ self.display())
  IArrows.append(self)
  if self.name[0:2]!="id":
   IEquations.append([eqnum, "("+self.name + " o " + self.source.identity.name+")", self.name])
   eqnum += 1
   IEquations.append([eqnum, "("+self.target.identity.name + " o " + self.name+")", self.name])
   eqnum += 1
  if self.name[0:2]=="id":
   IEquations.append([eqnum, "("+self.name + " o " + self.name+")", self.name])
   eqnum += 1


 def display(self):
  val = self.name    + " : "+ self.source.name + " -> " + self.target.name
  return val

def equations():
  for e in IEquations:
   print
   print str(e[0]+1) + ") "+ e[1] + " = " + e[2]
  return

def Sym(n):
 global IEquations
 global eqnum
 if n-1 <= len(IEquations):
  x = IEquations[n-1][1]
  y = IEquations[n-1][2]
  IEquations.append([eqnum, y,x])
  print("added: "+ y + " = " + x)
  eqnum += 1
  return

def Tr(n, m):
 global IEquations
 global eqnum
 if n-1 <= len(IEquations)  and  n-1 <= len(IEquations):
  if IEquations[n-1][2] and IEquations[m-1][1]:
   IEquations.append([eqnum, IEquations[n-1][1], IEquations[m-1][2] ])
   eqnum += 1
   print("added: " + IEquations[n-1][1] + " = " + IEquations[m-1][2])
   return


class Object:
 def __init__(self, name):
  global Objects
  global init
  self.name = name
  Objects.append(name)
  print ("added: "+ self.name)
  IObjects.append(self)
  Rules.append("Created "+name)
  self.identity = Arrow("id_"+self.name, self, self)
  if init != 0:
   self.true = Arrow("O_"+self.name, self, T)
  init = 1
  
T = Object("T")


def composition(arrow1,arrow2):
 if arrow2.target == arrow1.source:
  Arrow("("+arrow1.name + " o " + arrow2.name+")", arrow2.source, arrow1.target)
  Rules.append("Composed "+ arrow1.name + " and " + arrow2.name)
  return
 else:
  return 

class And:
 def __init__(self, object1,object2):
   Rules.append("Conjunction of "+ object1.name + " and " + object2.name)
   print("Conjunction of "+ object1.name + " and " + object2.name)
   self. object = Object("("+object1.name + " /\ " + object2.name+")")
   self. proj1 = Arrow("p1_" + self.object.name, self.object, object1)
   self. proj2 = Arrow("p2_" + self.object.name, self.object, object2)
   self. object1 = object1
   self. object2 = object2
   IUni.append(self)
   val = parse(" <= ", object1.name)
   if val!= []:
    if  len(val)> 1:
     if val[1] == object2.name:
      Arrow("e_"+val[0]+","+val[1], self.object, o(val[0]))
  

 def join(self, arrow1, arrow2):

   if arrow1.source == arrow2.source and arrow1.target == self.object1 and arrow2.target == self.object2:
    Rules.append("Joined " + arrow1.name + " and " + arrow2.name)
    print("Joined " + arrow1.name + " and " + arrow2.name)
    val = Arrow("< "+arrow1.name + " , "+ arrow2.name+ ">", arrow1.source, self.object)

    return val
   else:
    return None


class Implication:
 def __init__(self, object1,object2):
   Rules.append("Implication of "+ object1.name + " and " + object2.name)
   print("Implication of "+ object1.name + " and " + object2.name)
   self. object = Object("("+object1.name + " <= " + object2.name+")")
   self. object1 = object1
   self. object2 = object2
   IUni.append(self)

 def transpose(self, arrow):
  if parse(" /\ ",arrow.source.name)!= None and parse(" /\ ",arrow.source.name)[1] == self.object2.name:
   return Arrow("("+arrow.name+")*", o(parse(" /\ ",arrow.source.name)[0]),self.object)
  else:
   return None


def dis(l):
 for x in l:
  print x

def o(s):
 for o in IObjects:
  if o.name == s:
   return o

def a(s):
 for a in IArrows:
  if a.name == s:
   return a

def x(s):
 for x in IUni:
  if x.object.name == s:
   return x

def Join(arrow1,arrow2):
 x("("+a(arrow1).target.name+ " /\ " + a(arrow2).target.name+")").join(a(arrow1),a(arrow2))
 return



def Trans(arrow):  
 val = parse(" /\ ",a(arrow).source.name)
 if not("("+ a(arrow).target.name+" <= "+val[1]+")" in IUni):
  Imp(a(arrow).target.name,val[1]) 
 x("("+ a(arrow).target.name+" <= "+val[1]+")").transpose(a(arrow))
 Rules.append("Transposition of "+ a(arrow).display()) 
 return

def Obj(s):
 Object(s)
 return

def Conj(obj1,obj2):
 And(o(obj1),o(obj2))
 return

def Imp(obj1,obj2):
 Implication(o(obj1),o(obj2))
 return

def Comp(a1,a2):
 composition(a(a1),a(a2))
 return


def Hyp(name, obj1,obj2):
 print ("Hypothesis "),
 Arrow(name,o(obj1),o(obj2))
 return


def disp():
 print "Objects:     "
 print
 dis(Objects)
 print
 print "Arrows:     "
 print
 dis(Arrows)
 print
 print "Rules:      "
 print
 dis(Rules)

