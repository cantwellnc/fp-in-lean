-- Overloading + Typeclasses :)

-- typeclasses describe a collection of overloadable operations
-- to overload these ops for a new type, an instance is creaetd that contains an implementation
-- of each operation for the new type.

-- ex: Add describes types that allow addition,
-- and an instance Add Nat provides an implementation for Nats.

--  Unlike Java or C#'s interfaces, types can be given instances for type classes that the author of the type does not have access to.
-- og typeclasses paper: https://dl.acm.org/doi/epdf/10.1145/75277.75283


-- positive numbers

inductive Pos : Type where
  | one : Pos
  | succ : Pos -> Pos

-- this re presents positive nums, but it's not very convenient to use
-- can't use numeric literals

def s : Pos := 7

-- can't use operators
def fourteen : Pos := 7 + 7

-- Classes and Instances
-- a type class consists of a name, params,
-- and a collection of methods.
-- params: types for which overloadable ops are defined
-- methods: names + signatures of overloadable ops

class Plus (α : Type) where
  plus : α -> α -> α
-- type of Plus is Type -> Type

-- now we can "add" two nums
instance : Plus Nat where
  plus := Nat.add
-- methods are defined in a namespace with
-- the name of the typeclass, so let's open
-- it just to not have this be annoying

open Plus (plus)

#eval plus 7 7

-- now to use this typeclass for Pos, we just need
-- to define a plus fn on Pos

def Pos.plus : Pos -> Pos -> Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

#eval plus Pos.one Pos.one

-- no defn for floats, so err
#eval plus 5.2 917.25861

-- Overloading

-- you can overload Lean's add using a typeclass
-- called HAdd.
-- x + y = HAdd.hAdd x y
-- this is general and allows args to have different types

-- we'll implement a simpler one (Add) that requires
-- args to be of the same type. Lean will find this if HAdd is
-- not implemented.

instance : Add Pos where
  add := Pos.plus

def two : Pos := Pos.one + Pos.one

-- Converting to strings
-- used when IO.println is called on a value

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

instance : ToString Pos where
  toString := posToString true

-- ok, but overwhelming. every pos has a nat,
-- so why not translate them + then render

def Pos.toNat : Pos -> Nat
  | Pos.one => 1
  | Pos.succ n => 1 + n.toNat

instance : ToString Pos where
  toString x := toString (x.toNat)
-- notice, most recent impl for typecalss
-- takes precedence
#eval s!"There are {two}"


def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

-- similar to Add/HAdd, there is Mul/HMul
instance : Mul Pos where
  mul := Pos.mul

-- Literals
-- writing out constructors sucks.
-- we could convert any Nat to a Pos, but:
-- - Poss cannot represent 0, so conversion fn returns Option Pos
-- - you need to call a fn explicitly, not nice. bad api

-- There are 3 classes used to overload numeric literals:
-- Zero
class myZero (α : Type) where
  zero : α
-- One
class myOne (α : Type) where
  one : α
-- OfNat
class myOfNat (α : Type) (_ : Nat) where
  ofNat : α
-- α is the type being overloaded (Pos)
-- the ignored _ Nat arg is the literal we encountered.
-- it is there so that we can only define instances for those
-- values where the number makes sense (ex: 1, 2, 3, 4, ...)

-- this also means that type classes can depend on values, not just types
--  it allows the Lean standard library to arrange for there to be a Zero α instance whenever there's an OfNat α 0 instance, and vice versa

-- let's represent nums less than 4
inductive LT4 where
  | zero
  | one
  | two
  | three

instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three

#eval (3 : LT4)

-- out of bound not allowed
#eval (4 : LT4)


-- for Pos, OfNat should work for any Nat
-- other than Nat.zero. we can't write infinitely
-- many cases, so what do?

-- just like α can be an implicit arg to a fn, type classes also
-- take implicit args. Here, the Nat n (mentioned above) is implicit.
instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

def eight : Pos := 8
def zero : Pos := 0 -- can't make it!

-- Exercises

-- another way to rep a pos is as the succ of a Nat.
--
structure Pos2 where
  succ :: -- constructor to make a new struct, recall :)
  pred : Nat

def Pos2.add : Pos2 -> Pos2 -> Pos2
  | p1, p2 => Pos2.succ (1 + p1.pred + p2.pred)

instance: Add Pos2 where
  add := Pos2.add

def Pos2.mul : Pos2 -> Pos2 -> Pos2
  | p1, p2 => Pos2.succ (p1.pred * p2.pred + p1.pred + p2.pred)

instance: Mul Pos2 where
  mul := Pos2.mul

instance : OfNat Pos2 (n) where
  ofNat := {pred := n-1}

instance :  ToString Pos2 where
  toString p := toString (p.pred + 1)

#eval (7 : Pos2)
#eval (2 + 2 : Pos2)
#eval (0 : Pos2) -- evaluates to 1 always, even if it's written '0'
#eval (0 + 0 : Pos2) -- 2 ;)

-- only even numbers
structure Even where
  n : Nat -- the nat we're representing
  pf: (n % 2 == 0 : Prop) -- proof that the nat is even

#check Even.mk 1 (by decide) -- can't make non-even nums

#check Even.mk 2 (by decide) -- CAN make even nums

instance: Add Even where
  add := fun (e1 e2 : Even) =>
    let sum : Nat := e1.n + e2.n
    Even.mk sum (by
      have h1 : e1.n % 2 = 0 := by simpa using e1.pf
      have h2 : e2.n % 2 = 0 := by simpa using e2.pf
      grind)


def even2 := Even.mk 2 (by decide)
def even4 := Even.mk 4 (by decide)
#check (even2 +  even4).pf -- safe add


-- An HTTP request begins with an identification of a HTTP method,
--  such as GET or POST, along with a URI and an HTTP version.
--  Define an inductive type that represents an interesting subset of the HTTP methods,
-- and a structure that represents HTTP responses. Responses should have a ToString instance
-- that makes it possible to debug them. Use a type class to associate different IO actions
-- with each HTTP method, and write a test harness as an IO action that calls each method
-- and prints the result.


inductive Request (uri : Type) (body : Type) where
  | GET : uri -> Request uri body
  | POST : uri -> body ->  Request uri body
  | PUT : uri -> body -> Request uri body
  | DELETE : uri -> Request uri body

structure Response where
  status : Int
  body : String

instance : ToString Response where
  toString r := s!"\nRESPONSE:\nStatus: {r.status}\nBody: {r.body}"

class PrintHTTP α where
  runAndPrint : α -> IO Unit

def reqToRes : Request String String -> Response
  | Request.GET _ => {status := 200, body := ""}
  | Request.POST _ body => {status := 200, body := s!"ya posted this: {body}"}
  | Request.PUT _ body => {status := 200, body := s!"ya put this: {body}"}
  | Request.DELETE _ => {status := 200, body := ""}

-- duplication, can we get rid of that?
-- remember, if you want to bind in name then it MUST
-- be written like this
def runAndPrint (req : Request String String): IO Unit :=
  let respond := do IO.println (toString $ reqToRes req)
  match req with
    | Request.GET uri => do
      IO.println s!"GET {uri}"
      respond
    | Request.POST uri body => do
      IO.println s!"POST {uri} {body}"
      respond
    | Request.PUT uri body => do
      IO.println s!"PUT {uri} {body}"
      respond
    | Request.DELETE uri => do
      IO.println s!"DELETE: {uri}"
      respond

instance: PrintHTTP (Request String String) where
  runAndPrint := runAndPrint

#eval do {runAndPrint $ (Request.GET "/foo")}
#eval do {runAndPrint $ (Request.PUT "/foo" "{\"my\":\"body\"}")}
#eval do {runAndPrint $ (Request.POST "/foo" "{\"my\":\"body\"}")}
#eval do {runAndPrint $ (Request.DELETE "/foo")}
