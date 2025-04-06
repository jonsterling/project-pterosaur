import Pterosaur.RefinerTypes

variable [Monad m] [MonadState Theory m] [MonadExcept String m]

def checkObjectDict (selfName? : Option String) (tacs : List (Name × TermChecker m (n+1))) : ObjectDictChecker m n :=
  λ Γ =>
  let rec loop (spec : RecordSpec) (manifests primaries : Closure.Dict) tacs : RecordSpec → m (Term.Dict (n+1) × Term.Dict (n+1))
  | [] =>
    if Std.HashMap.isEmpty tacs then do
      let 𝕋 ← get
      return ⟨manifests.quote 𝕋 selfName?, primaries.quote 𝕋 selfName?⟩
    else throw s!"Redundant methods encountered: {tacs.keys}"
  | ⟨ℓ, cell⟩ :: methods =>
    match cell.manifest?, tacs[ℓ]? with
    | none, none => throw s!"Missing implementation of method {ℓ}"
    | some _, some _ => throw s!"Redundant implementation of method {ℓ}"
    | some clo, none => do
      loop (spec ++ [⟨ℓ, cell⟩]) (manifests ++ [⟨ℓ, clo⟩]) primaries (tacs.erase ℓ) methods
    | none, some tac => do
      let x := freshTranslucent n $ .obj none selfName? manifests primaries
      let typex := cell.type.inst (← get) x
      let tmx ← tac (Γ.ext selfName? (.rcdTp none selfName? spec) x) typex
      let clo := ⟨Γ.values, tmx⟩
      let cell := {cell with manifest? := some clo}
      loop (spec ++ [⟨ℓ, cell⟩]) manifests (primaries ++ [⟨ℓ, clo⟩]) (tacs.erase ℓ) methods
  loop [] [] [] $ Std.HashMap.ofList tacs
