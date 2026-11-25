set_option Elab.async false
namespace R2Q
inductive Q : Prop where
  | a : Q
  | mk : And Q Q → Q
theorem q_ok : Q := .mk ⟨.a, .a⟩
end R2Q
