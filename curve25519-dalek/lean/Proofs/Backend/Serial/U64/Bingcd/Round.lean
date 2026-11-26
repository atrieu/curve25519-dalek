module
public import Curve25519Dalek.Funs
public import Proofs.Helpers.Bingcd
import Proofs.Backend.Serial.U64.Bingcd.ApplyRow
import Proofs.Backend.Serial.U64.Bingcd.ApproxTop
import Proofs.Backend.Serial.U64.Bingcd.CofRow
import Proofs.Backend.Serial.U64.Bingcd.Inner
import Proofs.Backend.Serial.U64.Bingcd.Or4
public section

open Aeneas Aeneas.Std Result
open Bingcd

namespace Curve25519Dalek.backend.serial.u64.bingcd

/-- **A round is `Pornin.roundL`.** The Rust code reads the approximations from the limbs at
the top of `a | b`; they are those of `roundL` by `Pornin.approxL_eq_approxTop`. -/
@[step]
theorem round_spec (m : Array U64 4#usize) (ninv : U64) (s : State) :
    round m ninv s ⦃ r => r.toL = Pornin.roundL 31 (L4 m) ninv.bv s.toL ⦄ := by
  unfold round
  step*
  obtain ⟨ha, hb⟩ := Pornin.approxL_eq_approxTop (w := 64) (K := 31) rfl (L4 s.a) (L4 s.b)
  rw [ab_post, ← ha] at i_post
  rw [ab_post, ← hb] at i1_post
  simp only [State.toL, Pornin.roundL, a1_post, a_post, b1_post, a2_post, na_post, nb_post,
    t_post, t_post1, t_post2, t_post3, i_post, i1_post, U64.bv]

end Curve25519Dalek.backend.serial.u64.bingcd
