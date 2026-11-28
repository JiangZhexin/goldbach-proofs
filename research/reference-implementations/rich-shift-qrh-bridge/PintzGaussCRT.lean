import PintzPoleEuler
import PintzPrimePowerGauss

noncomputable section
open Finset PintzPoleEuler
namespace PintzGaussCRT

def trans {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (χ : MulChar S ℂ) :
    MulChar R ℂ where
  toFun a := χ (e a)
  map_one' := by simp
  map_mul' := by simp
  map_nonunit' a ha := MulChar.map_nonunit _ (fun H => ha (by simpa using H.map e.symm))

def leftMul {R S : Type*} [CommRing R] [CommRing S] (χ : MulChar (R × S) ℂ) :
    MulChar R ℂ where
  toFun x := χ (x,1)
  map_one' := χ.map_one
  map_mul' x y := by simpa using χ.map_mul (x,1) (y,1)
  map_nonunit' x hx := χ.map_nonunit (fun h => hx (Prod.isUnit_iff.mp h).1)

def rightMul {R S : Type*} [CommRing R] [CommRing S] (χ : MulChar (R × S) ℂ) :
    MulChar S ℂ where
  toFun y := χ (1,y)
  map_one' := χ.map_one
  map_mul' x y := by simpa using χ.map_mul (1,x) (1,y)
  map_nonunit' x hx := χ.map_nonunit (fun h => hx (Prod.isUnit_iff.mp h).2)

theorem mulChar_prod {R S : Type*} [CommRing R] [CommRing S] (χ : MulChar (R × S) ℂ)
    (x : R) (y : S) : χ (x,y) = leftMul χ x * rightMul χ y := by
  change χ (x,y) = χ (x,1) * χ (1,y)
  rw [← map_mul]
  simp

theorem gauss_prod {R S : Type*} [CommRing R] [CommRing S] [Fintype R] [Fintype S]
    (χ : MulChar (R × S) ℂ) (ψ : AddChar (R × S) ℂ) (x : R) (y : S) :
    gaussSum χ (ψ.mulShift (x,y)) =
      gaussSum (leftMul χ) ((leftChar ψ).mulShift x) *
        gaussSum (rightMul χ) ((rightChar ψ).mulShift y) := by
  unfold gaussSum
  rw [Fintype.sum_prod_type, sum_mul]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  simp only [AddChar.mulShift_apply, Prod.mk_mul_mk, mulChar_prod χ a b,
    character_prod ψ (x*a) (y*b)]
  ring

theorem transport {R S : Type*} [CommRing R] [CommRing S] [Fintype R] [Fintype S]
    (e : R ≃+* S) (χ : MulChar S ℂ) (ψ : AddChar S ℂ) (x : R) :
    gaussSum χ (ψ.mulShift (e x)) =
      gaussSum (trans e χ) ((ψ.compAddMonoidHom e.toAddMonoidHom).mulShift x) := by
  unfold gaussSum
  rw [← e.toEquiv.sum_comp]
  apply sum_congr rfl
  intro a _
  simp [trans, AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply]

theorem exact_crt {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) (ψ : AddChar (ZMod (m*n)) ℂ)
    (t : ZMod m × ZMod n) :
    let e := (ZMod.chineseRemainder h).symm
    let χ' := trans e χ
    let ψ' := ψ.compAddMonoidHom e.toAddMonoidHom
    gaussSum χ (ψ.mulShift (e t)) =
      gaussSum (leftMul χ') ((leftChar ψ').mulShift t.1) *
      gaussSum (rightMul χ') ((rightChar ψ').mulShift t.2) := by
  dsimp only
  rw [transport]
  obtain ⟨x,y⟩ := t
  exact gauss_prod _ _ _ _

def leftUnit {m n : ℕ} (h : m.Coprime n) : (ZMod m)ˣ :=
  (ZMod.unitOfCoprime n h.symm)⁻¹

def rightUnit {m n : ℕ} (h : m.Coprime n) : (ZMod n)ˣ :=
  (ZMod.unitOfCoprime m h)⁻¹

theorem left_add_normalize {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n) :
    leftChar (ZMod.stdAddChar.compAddMonoidHom (ZMod.chineseRemainder h).symm.toAddMonoidHom) =
      ZMod.stdAddChar.mulShift (leftUnit h) := by
  let : NeZero (m*n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  ext x
  let y : ZMod m := (leftUnit h : ZMod m) * x
  have hy : (n : ZMod m) * y = x := by
    dsimp [y]
    rw [← mul_assoc, ← ZMod.coe_unitOfCoprime n h.symm, leftUnit, ← Units.val_mul]
    simp
  have hcrt : (ZMod.chineseRemainder h).symm (x,0) = ((n*y.val : ℕ): ZMod (m*n)) := by
    apply (ZMod.chineseRemainder h).injective
    rw [RingEquiv.apply_symm_apply, map_natCast]
    apply Prod.ext
    · simpa [Nat.cast_mul] using hy.symm
    · simp [Nat.cast_mul]
  change ZMod.stdAddChar ((ZMod.chineseRemainder h).symm (x,0)) = ZMod.stdAddChar y
  rw [hcrt, ← ZMod.natCast_zmod_val y, PintzEightGauss.stdAddChar_nat_fraction,
    PintzEightGauss.stdAddChar_nat_fraction]
  apply congrArg PintzEightGauss.additivePhase
  push_cast
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp
  rw [ZMod.natCast_zmod_val]

theorem right_add_normalize {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n) :
    rightChar (ZMod.stdAddChar.compAddMonoidHom (ZMod.chineseRemainder h).symm.toAddMonoidHom) =
      ZMod.stdAddChar.mulShift (rightUnit h) := by
  let : NeZero (m*n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  ext x
  let y : ZMod n := (rightUnit h : ZMod n) * x
  have hy : (m : ZMod n) * y = x := by
    dsimp [y]
    rw [← mul_assoc, ← ZMod.coe_unitOfCoprime m h, rightUnit, ← Units.val_mul]
    simp
  have hcrt : (ZMod.chineseRemainder h).symm (0,x) = ((m*y.val : ℕ): ZMod (m*n)) := by
    apply (ZMod.chineseRemainder h).injective
    rw [RingEquiv.apply_symm_apply, map_natCast]
    apply Prod.ext
    · simp [Nat.cast_mul]
    · simpa [Nat.cast_mul] using hy.symm
  change ZMod.stdAddChar ((ZMod.chineseRemainder h).symm (0,x)) = ZMod.stdAddChar y
  rw [hcrt, ← ZMod.natCast_zmod_val y, PintzEightGauss.stdAddChar_nat_fraction,
    PintzEightGauss.stdAddChar_nat_fraction]
  apply congrArg PintzEightGauss.additivePhase
  push_cast
  have hm : (m:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  field_simp
  rw [ZMod.natCast_zmod_val]

theorem unit_norm_shift {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (u : (ZMod m)ˣ) (x : ZMod m) :
    ‖gaussSum χ ((ZMod.stdAddChar.mulShift u).mulShift x)‖ =
      ‖gaussSum χ (ZMod.stdAddChar.mulShift x)‖ := by
  have he : (ZMod.stdAddChar.mulShift u).mulShift x = (ZMod.stdAddChar.mulShift x).mulShift u := by
    rw [AddChar.mulShift_mulShift, AddChar.mulShift_mulShift, mul_comm (u : ZMod m)]
  rw [he, gaussSum_mulShift_eq, norm_mul, (χ⁻¹).unit_norm_eq_one u, one_mul]

theorem norm_crt {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) (x : ZMod m) (y : ZMod n) :
    let e := (ZMod.chineseRemainder h).symm
    let χ' := trans e χ
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (e (x,y)))‖ =
      ‖gaussSum (leftMul χ') (ZMod.stdAddChar.mulShift x)‖ *
        ‖gaussSum (rightMul χ') (ZMod.stdAddChar.mulShift y)‖ := by
  dsimp only
  rw [exact_crt, norm_mul, left_add_normalize h, right_add_normalize h, unit_norm_shift, unit_norm_shift]

theorem norm_crt_nat {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) (k : ℕ) :
    let χ' := trans (ZMod.chineseRemainder h).symm χ
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (k : ZMod (m*n)))‖ =
      ‖gaussSum (leftMul χ') (ZMod.stdAddChar.mulShift (k : ZMod m))‖ *
        ‖gaussSum (rightMul χ') (ZMod.stdAddChar.mulShift (k : ZMod n))‖ := by
  have E : (ZMod.chineseRemainder h).symm ((k : ZMod m),(k : ZMod n)) = (k : ZMod (m*n)) := by
    change (ZMod.chineseRemainder h).symm (k : ZMod m × ZMod n) = _
    exact map_natCast _ _
  simpa only [E] using norm_crt h χ (k : ZMod m) (k : ZMod n)

theorem norm_crt_neg {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) (k : ℕ) :
    let χ' := trans (ZMod.chineseRemainder h).symm χ
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(k : ZMod (m*n))))‖ =
      ‖gaussSum (leftMul χ') (ZMod.stdAddChar.mulShift (-(k : ZMod m)))‖ *
        ‖gaussSum (rightMul χ') (ZMod.stdAddChar.mulShift (-(k : ZMod n)))‖ := by
  have E : (ZMod.chineseRemainder h).symm (-(k : ZMod m),-(k : ZMod n)) = -(k : ZMod (m*n)) := by
    change (ZMod.chineseRemainder h).symm (-(k : ZMod m × ZMod n)) = _
    rw [map_neg, map_natCast]
  simpa only [E] using norm_crt h χ (-(k : ZMod m)) (-(k : ZMod n))

#print axioms norm_crt_neg
#print axioms norm_crt
#print axioms exact_crt
end PintzGaussCRT
