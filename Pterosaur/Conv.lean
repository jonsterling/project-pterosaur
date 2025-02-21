import Pterosaur.Prelude
import Pterosaur.Bwd
import Pterosaur.Term
import Pterosaur.Value
import Pterosaur.Eval
import Pterosaur.Quote
import Pterosaur.Theory

variable [Monad m] [MonadExcept String m]
variable (𝕋 : Theory)

mutual
  partial
  def Value.isIrrelevant (n : Nat) : Value → Bool
  | .neu _ (.translucent V) =>
    V.get.isIrrelevant n
  | .prod _ A B =>
    let x := fresh n A
    let Bx := B.inst 𝕋 x
    Bx.isIrrelevant (n+1)

  | .sum locale? selfName? methods =>
    let x := fresh n $ .sum locale? selfName? methods
    List.all methods λ ⟨_, cell⟩ =>
    match cell.manifest? with
    | some _ => true
    | none =>
      let typex := cell.type.inst 𝕋 x
      typex.isIrrelevant (n+1)

  | _ => false
end

mutual
  partial
  def Value.convert (n : Nat) : Value → Value → m Unit
  | .neu _ (.translucent V0), V1 => Value.convert n V0.get V1
  | V0, .neu _ (.translucent V1) => Value.convert n V0 V1.get
  | .neu N0 (.abstract A), .neu N1 _ =>
    match A.get.isIrrelevant 𝕋 n with
    | true => return ()
    | false => Neutral.convert n N0 N1

  | .prod _ A0 B0, .prod _ A1 B1 => do
    Value.convert n A0 A1
    let x := fresh n A0
    Value.convert (n+1) (B0.inst 𝕋 x) (B1.inst 𝕋 x)

  | .sum locale0? selfName? (methods0 : RecordSpec), .sum locale1? _ (methods1 : RecordSpec) =>
    if locale0? == locale1?
    then RecordSpec.convert n selfName? methods0 methods1
    else throw "Value.convert: mismatched locale names"

  | .lam _ A M, V => do
    let x := fresh n A.get
    Value.convert (n+1) (M.inst 𝕋 x) (Value.apply 𝕋 V x)

  | V, .lam _ A M => do
    let x := fresh n A.get
    Value.convert (n+1) (Value.apply 𝕋 V x) (M.inst 𝕋 x)

  | V0@(.obj _ _ _ methods), V1 =>
    for ⟨name, _⟩ in methods do
      Value.convert n (V0.call 𝕋 name) (V1.call 𝕋 name)

  | V0, V1@(.obj _ _ _ methods) =>
    for ⟨name,  _⟩ in methods do
      Value.convert n (V0.call 𝕋 name) (V1.call 𝕋 name)

  | .TYPE, .TYPE => return ()
  | .error _, _ => return ()
  | _, .error _ => return ()
  | V0, V1 => throw s!"Conversion failed: {reprStr V0} vs. {reprStr V1}"

  partial
  def RecordSpec.convert (n : Nat) (selfName? : Option String) : (methods0 methods1 : RecordSpec) → m Unit :=
    let rec loop (Self : RecordSpec) : (methods0 methods1 : RecordSpec) → m Unit
    | [], [] => pure ()
    | ⟨method0, type0, manifest0?⟩ :: methods0, ⟨method1, type1, manifest1?⟩ :: methods1 =>
      if method0 == method1
      then do
        let x := fresh n $ .sum none selfName? Self
        let type0x := type0.inst 𝕋 x
        let type1x := type1.inst 𝕋 x
        Value.convert (n+1) type0x type1x
        let () ← do
          let Vx0? := manifest0?.map λ mfst => mfst.inst 𝕋 x
          let Vx1? := manifest1?.map λ mfst => mfst.inst 𝕋 x
          match Vx0?, Vx1? with
          | some Vx0, some Vx1 =>
            Value.convert (n+1) Vx0 Vx1
          | none, none => pure ()
          | _, _ => if type0x.isIrrelevant 𝕋 (n+1) then pure () else throw "RecordSpec.convert: manifest mismatch"
        loop (Self ++ [⟨method0, type0, manifest0?⟩]) methods0 methods1
      else throw "RecordSpec.convert: mismatched methods"
    | _, _ => throw "RecordSpec.convert: different lengths"
    loop []

  partial
  def Value.Dict.convert (n : Nat) (dict0 dict1 : Value.Dict) : m Unit :=
    let rec loop (dict0 : Value.Dict) (hdict1 : Std.HashMap Name Value) : m Unit :=
      match dict0 with
      | [] =>
        if Std.HashMap.isEmpty hdict1 then return ()
        else throw "ValueDict.convert: second dictionary had extraneous methods"
      | ⟨name, V0⟩ :: dict0 =>
        match hdict1[name]? with
        | none => throw s!"ValueDict.convert: second dictionary lacked method `{name}`"
        | some V1 => do
          Value.convert n V0 V1
          loop dict0 $ hdict1.erase name
    ;
    loop dict0 (Std.HashMap.ofList dict1)

  partial
  def Neutral.convert (n : Nat) (N0 N1 : Neutral Value) : m Unit := do
    Nut.convert N0.nut N1.nut
    Spine.convert n N0.frames N1.frames

  partial
  def Spine.convert (n : Nat) : Spine len0 → Spine len1 → m Unit
  | .emp, .emp => return ()
  | .snoc frames0 frame0, .snoc frames1 frame1 => do
    Spine.convert n frames0 frames1
    Frame.convert n frame0 frame1
  | _, _ => throw "convertFrames: length mismatch"

  partial
  def Frame.convert (n : Nat) : Frame Value → Frame Value → m Unit
  | .appTo V0, .appTo V1 =>
    Value.convert n V0 V1
  | .call name0, .call name1 =>
    if name0 == name1 then return () else
    throw "Frame.convert: method calls"
  | _, _ =>
    throw "Frame.convert: mismatched frames"

  partial
  def Nut.convert : Nut → Nut → m Unit
  | .localVar l0, .localVar l1 =>
    if l0 = l1 then return () else throw s!"convertNut: mismatched local variables {l0} vs. {l1}"
  | .globalVar n0, .globalVar n1 =>
    if n0 == n1 then return () else throw "convertNut: mismatched global variables"
  | _, _=> throw "convertNut: tried to convert local variable with global variable"

end
