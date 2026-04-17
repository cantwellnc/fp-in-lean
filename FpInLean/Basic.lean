#eval String.append "a" (String.append "b" "c")

#eval 42 + 19

#eval String.append "A" (String.append "B" "C")
#eval String.append (String.append "A" "B") "C"
#eval if 3 == 3 then 5 else 7
#eval if 3 == 4 then "equal" else "not equal"


#eval (1-2 : Nat)

#eval (1-2 : Int)

#check (1-2 : Int)

-- #check String.append ["hello", ""] ""


-- functions are introed using the 'def' keyword
def helloTo you := String.append "Hello, " you

-- but you can also directly refer to values by names,
-- this is NOT a zero-arg fn
def hello := "Hello"


def joinStringsWithString (s1 : String ) (s2: String) (s3: String) : String :=
  s2 ++ s1 ++ s3

#eval joinStringsWithString "a" "b" "c"


#check joinStringsWithString ":"


def volume (height width depth : Nat) : Nat :=
  height * width * depth


#eval volume 1 2 3


-- defining types

-- alias
def Str : Type := String

-- The reason this works is that types follow the same rules as the rest of Lean.
-- Types are expressions, and in an expression,
-- a defined name can be replaced with its definition.
-- can also use abbrev

abbrev N : Type := Nat


-- structures
-- Defining a structure introduces a completely new type to Lean that can't be reduced to any other type
#check 1.2
#check -454.32324241
-- decimal point => Float
-- otherwise you need a type annotation
#check 0
#check (0 : Float)


-- point

structure Point where
  x : Float
  y : Float

-- constructing
-- note: the type annotation tells lean what structure
-- you are trying to construct
def origin : Point := {x := 0, y:= 0}

#eval origin.x

def addPoints (p1 p2 : Point) : Point :=
  {x := p1.x + p2.x, y := p1.y + p2.y}

-- checking like this is also valid (note the type hint inside the brackets)
#check { x := 0.0, y := 0.0 : Point}

-- updating

def zeroX (p : Point) : Point :=
  {x := 0, y := p.y}
-- naive ^^, if we add a field to point then this defn has
-- to be updated

-- instead, idiomatic way is to use 'with' syntax

def zeroX2 (p : Point) : Point :=
  {p with x:= 0} -- retain all fields of p, only changing x

-- constructors
-- every structure has a built-in constructor. you cannot change it
-- like you can in ex: python

#check Point.mk 1 2 -- for a structure S, this constructor is called mk
-- not good style to use it tho, use brackets

#check Point.mk -- (x y : Float) : Float

-- you can override a constructor's name, but that's it
-- ex: convert Point.mk to Point.point:
structure Point2 where
  point ::
  x : Float
  y : Float

-- the accessors x, y are also fns (but in the structure's namespace)
#check Point.x -- (self : Point) : Float

-- accessor . notation can be used for things other than struct fields
-- you can define it for any type.

-- TARGET.f ARG1 ARG2 ... will substitute TARGET in as left-most arg of T, and then call f with ARG1 ARG2 etc..

-- String is not a struct with a field called 'append', but
-- we can call String.append like this:
#eval "one".append "two" -- "onetwo"


def Point.map (f : Float -> Float) (p : Point ) : Point :=  -- note: p is not leftmost, but there's only one place to put it
  {x := f p.x, y := f p.y}

def fourAndThree : Point := {x := 4, y := 3}

#eval fourAndThree.map Float.sin


-- exercises

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

def volume2 (p : RectangularPrism) : Float :=
  p.height * p.width * p.depth

#eval volume2 ({height := 2, width := 1 , depth := 2 : RectangularPrism})


structure Segment where
  lSide : Float
  rSide : Float

def length (s : Segment) : Float :=
  s.rSide - s.lSide

#eval length ({lSide := 0, rSide := 1 : Segment})

-- RectangularPrism intros: RectangularPrism.{mk, depth, width, heigh}


-- structures are known as product types.
-- data structures that allow choices are sum types.
-- data structures that can include instances of themselves are recursive datatypes.
-- recursive sum types are called INDUCTIVE datatypes.

-- Bool is inductive
inductive MyBool where
  | false : MyBool -- each of these are type constructors
  | true : MyBool

-- note that you may have multiple constructors for a single
-- inductive dt, UNLIKE structures.
-- constructors are placed in the namespace of the type, just like structures.


-- Natural numbers are also inductive

inductive MyNat where
  | zero : MyNat -- you're either 0
  | succ (n : MyNat) : MyNat -- or 1 + (a natural number)

#eval (Nat.succ (Nat.succ (Nat.succ Nat.zero)) = 3)


-- pattern matching

def isZero (n : Nat) : Bool :=
  match n with
    | Nat.zero => true
    | Nat.succ k => false

#eval isZero 0
#eval isZero 1


-- predecessor
def pred (n : Nat) : Nat :=
  match n with
    | Nat.zero => n
    | Nat.succ k => k

#eval (pred 2 = 1) -- equality check
-- same thing: is the proposition (pred 2 = 1) true?
#eval (pred 2 = 1 : Prop) = true

#eval pred 0 -- 0

-- you can match on structs too!

def depth (p : RectangularPrism) : Float :=
  match p with
    | {height := _, width := _, depth := d} => d
    -- you can't use {p with depth := d} tho :(


-- recursive fns are good for dealing w recursive data

def even (n : Nat) : Bool :=
  match n with
    | Nat.zero => true
    | Nat.succ k => not (even k) -- wow that is beautiful
-- this type of fn is known as doing "structural recursion" since we specify what to do
-- for each constructor of Nat


-- lean will reject infinitely looping programs like this one that accidentally
-- calls even with the original number instead of k
def evenLoop (n : Nat) : Bool := -- "failed to show termination"
  match n with
    | Nat.zero => true
    | Nat.succ _ => not (evenLoop n)
-- lean wants every function to provably terminate by reaching a base case when
-- doing structural recursion


def add (n k : Nat) : Nat :=
  match k with
    | Nat.zero => n
    | Nat.succ k' => Nat.succ (add n k')
-- n + k = succ(succ(... k times ... (n)))


def mult (n k : Nat) : Nat :=
  match k with
    | Nat.zero => Nat.zero -- add n to itself k times
    | Nat.succ k' => add n (mult n k') -- n + n*k-1

#eval mult 3 4


-- div is not structurally recursive so lean can't prove that it terminates.
def div (n : Nat) (k : Nat) : Nat :=
  if n < k then -- not matching on constructors!
    0
  else Nat.succ (div (n - k) k) -- arg is


-- polymorphism

--let's make a polymorphic point that can use floats or ints or whatever

structure PPoint (α : Type) where
  x : α
  y : α

-- you can concretize to a particular type

def origin2 : PPoint Nat := { x:= 0, y:=0 }
#check origin2

-- defns can take types are arguments, so they are also polymorphic.

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  {point with x:= newX}
-- Polymorphic functions work by taking a named type argument and having later types refer to the argument's name.
-- there's no ad-hoc reason for how types can be named + passed around.
-- lean can compute on types! for instance, we can write the type for a function
-- that takes a Sign (pos | neg) will return a nat or an int depending on the sign.

inductive Sign where
 | pos
 | neg

def posOrNegThree (s : Sign) :
  match s with | Sign.pos => Nat | Sign.neg => Int
  -- whaaaaaat, you can pattern match in the type signature
  :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

-- question: can i write the type of this function separetly from
-- the impl? I can't seem to find the right way to do so..
