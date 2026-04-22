-- Running + compiling a program

def main : IO Unit := IO.println "Hello, world!"
-- lean --run HelloWorld.lean
-- main has a description of effects to be carried out

-- Unit () is the simplest inductive type. 1 constructor (unit)
-- with no args. the lack of interesting arguments or return values can be signaled by using the Unit type instead


-- IO α is the type of a prog that when executed will
-- throw an exception OR return an α. It may perform
-- side effects aka IO Actions. Lean distinguishes between this
-- and evaluation of expressions.

-- Ex: IO.println : String -> IO Unit

-- FP vs effects

-- How can a language in which the same expression always yields the same result
-- support programs that read files from disk, when the contents of these files
-- might change over time?

-- This apparent contradiction can be resolved by thinking a bit differently
-- about side effects. Imagine a café that sells coffee and sandwiches.
-- This café has two employees: a cook who fulfills orders, and a worker at
-- the counter who interacts with customers and places order slips.
-- The cook is a surly person, who really prefers not to have any contact
-- with the world outside, but who is very good at consistently delivering
-- the food and drinks that the café is known for. In order to do this, however,
-- the cook needs peace and quiet, and can't be disturbed with conversation.
--  The counter worker is friendly, but completely incompetent in the kitchen.
-- Customers interact with the counter worker, who delegates all actual cooking
-- to the cook. If the cook has a question for a customer, such as clarifying an allergy,
-- they send a little note to the counter worker, who interacts with the customer and passes
-- a note back to the cook with the result.

-- another perspective:
-- action = fn that takes world + returns (value, new world)
-- with that frame,  reading a line of text from standard input is a pure function,
-- the entire universe cannot be turned into a Lean value and placed into memory.

-- However, it is possible to implement a variation of this model with an abstract
-- token that stands for the world. When the program is started, it is provided with
--  a world token. This token is then passed on to the IO primitives, and their returned
-- tokens are similarly passed to the next step. At the end of the program, the token is
-- returned to the operating system.


-- Combining IO actions with do

def main2 : IO Unit := do
-- get handles
  let stdin <- IO.getStdin -- local vars with let
  let stdout <- IO.getStdout
  -- or actions
  stdout.putStrLn "How would you like to be addressed?"
  let input <- stdin.getLine
  -- pure val so no <-
  let name :=  input.dropRightWhile Char.isWhitespace
  stdout.putStrLn s!"Hello, {name}"


-- Ordinarily, the local definition in a let can be used in just one expression,
-- which immediately follows the local definition.

-- in do-notation, let makes the bound value available in ALL subsequent
-- exprs in the do-block.

-- IO actions as values
-- why make distinction between evaluating exprs +
-- executing IO actions?


-- The ability to mention an action without carrying it out
--  allows ordinary functions to be used as control structures.
def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure () -- no action
  | n + 1 => do
    action -- do action
    nTimes action n

#eval nTimes (IO.println "aye") 2

-- IO actions are values, so we can store them too

def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def from5 : List (IO Unit) := countdown 5

#eval from5.length -- 6

-- creates 1 big action from a list of actions
def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions

-- putting it a fn of type IO Unit will run it :)
def main3 : IO Unit := runActions from5
#eval main3


-- exercises

-- understand the following program
def main4 : IO Unit := do
  let englishGreeting := IO.println "Hello!" -- binds action to var
  IO.println "Bonjour!" -- evals expr + then performs action
  englishGreeting -- evals expr + performs action
-- expected:
-- "Bonjour!"
-- "Hello!"

#eval main4


-- more do notation conveniences

partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    (← IO.getStdout).write buf -- instead of assigning stdout to a var + then immediately using it, just do this
    dump stream

-- IO actions that Lean lifts from a nested expression context are called "nested actions".
-- #eval both evaluates the provided expression and executes the resulting action value
