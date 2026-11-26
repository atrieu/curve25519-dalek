module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd32
import Proofs.Backend.Serial.U32.Bingcd.ApplyRow
import Proofs.Backend.Serial.U32.Bingcd.ApproxTop
import Proofs.Backend.Serial.U32.Bingcd.CofRow
import Proofs.Backend.Serial.U32.Bingcd.Inner
import Proofs.Backend.Serial.U32.Bingcd.Or8
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u32.bingcd

/-- **A round is `Pornin.roundL`.** The Rust code reads the approximations from the limbs at
the top of `a | b`; they are those of `roundL` by `Pornin.approxL_eq_approxTop`. -/
@[step]
theorem round_spec (m : Array U32 8#usize) (ninv : U32) (s : State) :
    round m ninv s ⦃ r => r.toL = Pornin.roundL 15 (L8 m) ninv.bv s.toL ⦄ := by
  unfold round
  step*
  obtain ⟨ha, hb⟩ := Pornin.approxL_eq_approxTop (w := 32) (K := 15) rfl (L8 s.a) (L8 s.b)
  rw [ab_post, ← ha] at i_post
  rw [ab_post, ← hb] at i1_post
  simp only [State.toL, Pornin.roundL, a1_post, a_post, b1_post, a2_post, na_post, nb_post,
    t_post, t_post1, t_post2, t_post3, i_post, i1_post, U32.bv]

end Curve25519Dalek.backend.serial.u32.bingcd
