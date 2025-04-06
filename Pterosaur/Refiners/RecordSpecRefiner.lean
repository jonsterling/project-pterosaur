import Pterosaur.RefinerTypes

variable [Monad m] [MonadState Theory m] [MonadExcept String m]

namespace RecordSpecRefiner

def refine (selfName? : Option String) (tacs : List (Name × TermChecker m (n+1))) : RecordSpecRefiner m n :=
  λ Γ =>
  let rec loop (Self : RecordSpec) (tacs : Std.HashMap Name (TermChecker m (n+1))): RecordSpec → m RecordSpec
  | [] =>
    if Std.HashMap.isEmpty tacs
    then return Self
    else throw s!"Redundant methods encountered: {tacs.keys}"
  | ⟨ℓ, type, manifest?⟩ :: methods => do
    match tacs[ℓ]? with
    | none => loop (Self ++ [⟨ℓ, type, manifest?⟩]) tacs methods
    | some tac =>
      match manifest? with
      | some _ => throw "RecordSpecRefiner.refine: refining already-refined method"
      | none => do
        let tpSelf := Value.rcdTp none selfName? Self
        let x := fresh n tpSelf
        let typex := type.inst (← get) x
        let Γ' := Γ.ext selfName? tpSelf x
        let tmImpl ← tac Γ' typex
        loop (Self ++ [⟨ℓ, type, some ⟨Γ.values, tmImpl⟩⟩]) (tacs.erase ℓ) methods
  ;
  loop [] (Std.HashMap.ofList tacs)
