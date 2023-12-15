import Lean

open Lean Meta

namespace DisplayAlias

structure State where 
  aliases : PersistentHashMap String Nat
  nextName : Nat
deriving Inhabited 

def initialState : State where 
  aliases := PersistentHashMap.empty
  nextName := 0
  
initialize Extension :
    EnvExtension State ← registerEnvExtension (pure initialState)

def addLabel (label : String) : CoreM Unit := do
  let env := EnvExtension.modifyState Extension (← getEnv) (fun ⟨aliases, nextName⟩  => 
    let newAliases := aliases.insert label nextName
    ⟨newAliases, nextName+1⟩ 
  )
  setEnv env

def generateName : Nat → String  
  | 0 => "A"
  | 1 => "B"
  | 2 => "C"
  | 3 => "D"
  | 4 => "E"
  | 5 => "F"
  | 6 => "G"
  | 7 => "H"
  | _ => "I"

private def getAliases : CoreM (PersistentHashMap String Nat) := do 
  let ⟨aliases, _⟩  := EnvExtension.getState Extension (← getEnv) 
  return aliases

def getAlias? (label : String) : CoreM (Option String) := do 
  let aliases ← getAliases 
  let some nameIndex := aliases.find? label | return none
  return some (generateName nameIndex)

def getAllAliases : CoreM (List (String × String)) := do
  let aliasList := (← getAliases).toList 
  let replaceIndexWithName : (String × Nat) → (String × String) := 
    fun (label, nameIndex) => (label, generateName nameIndex)
  return aliasList.map replaceIndexWithName

def printAllAliases : CoreM Unit := do 
  dbg_trace (← getAllAliases)
