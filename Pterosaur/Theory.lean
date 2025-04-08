import Pterosaur.Name
import Pterosaur.Value
import Pterosaur.Term
import Std.Data.HashSet

structure Defined where
  value : Value
  type : Value
deriving Repr, Nonempty

structure TypedTerm (n : Nat) where
  term : Term n
  type : Value
deriving Repr, Nonempty

structure LocaleExtension where
  type : Closure Value
  impl : Closure Value
deriving Repr, Nonempty

structure LocaleSpec where
  selfName? : Option String
  spec : RecordSpec
  extensions : Std.HashMap Name LocaleExtension := {}
  importedBy : Array (Name × Value) := #[]
deriving Repr, Nonempty

inductive Entry where
| translucent (E : Defined)
| abstract (type : Value)
deriving Repr, Nonempty

structure Theory where
  globals : Std.HashMap Name Entry
  locales : Std.HashMap Name LocaleSpec
  revelations : Std.HashSet Name
deriving Repr, Nonempty

def Theory.insertGlobal (name : Name) (E : Entry) (𝕋 : Theory) : Theory :=
  { 𝕋 with globals := 𝕋.globals.insert name E }

def Theory.insertLocale (name : Name) (L : LocaleSpec) (𝕋 : Theory) : Theory :=
  { 𝕋 with locales := 𝕋.locales.insert name L }

instance : EmptyCollection Theory where
  emptyCollection := ⟨{}, {}, {}⟩

def Theory.getValue (𝕋 : Theory) (x : Name) : Option Value :=
  match 𝕋.globals[x]? with
  | none => none
  | some (.translucent defn) => some defn.value
  | some (.abstract _) => none

def Theory.getBoundary (𝕋 : Theory) (x : Name) : Option (Boundary Value) :=
  match 𝕋.globals[x]? with
  | none => none
  | some (.translucent defn) => some (.translucent defn.value)
  | some (.abstract type) => some (.abstract type)

def Theory.getLocaleSpec (𝕋 : Theory) (l : Name) : Option LocaleSpec :=
  𝕋.locales[l]?
