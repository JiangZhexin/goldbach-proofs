import PintzGaussCRT

noncomputable section
open PintzGaussCRT
namespace PintzCRTConductor

abbrev left {m n : ℕ} (h : m.Coprime n) (χ : DirichletCharacter ℂ (m*n)) :
    DirichletCharacter ℂ m := leftMul (trans (ZMod.chineseRemainder h).symm χ)

abbrev right {m n : ℕ} (h : m.Coprime n) (χ : DirichletCharacter ℂ (m*n)) :
    DirichletCharacter ℂ n := rightMul (trans (ZMod.chineseRemainder h).symm χ)

theorem cast_crt {a b m n : ℕ} [NeZero (m*n)] (hab : a.Coprime b)
    (hmn : m.Coprime n) (ha : a ∣ m) (hb : b ∣ n) (x : ZMod (m*n)) :
    ZMod.chineseRemainder hab (ZMod.cast x : ZMod (a*b)) =
      ((ZMod.cast (ZMod.chineseRemainder hmn x).1 : ZMod a),
        (ZMod.cast (ZMod.chineseRemainder hmn x).2 : ZMod b)) := by
  rw [← ZMod.natCast_zmod_val x, ZMod.cast_natCast (Nat.mul_dvd_mul ha hb), map_natCast, map_natCast]
  apply Prod.ext
  · exact (ZMod.cast_natCast ha _).symm
  · exact (ZMod.cast_natCast hb _).symm

theorem left_changeLevel {a b m n : ℕ} [NeZero (m*n)] (hab : a.Coprime b)
    (hmn : m.Coprime n) (ha : a ∣ m) (hb : b ∣ n) (χ : DirichletCharacter ℂ (a*b)) :
    left hmn (DirichletCharacter.changeLevel (Nat.mul_dvd_mul ha hb) χ) =
      DirichletCharacter.changeLevel ha (left hab χ) := by
  ext1 x
  let e := (ZMod.chineseRemainder hmn).symm
  let y := e (↑x, 1)
  have hy : IsUnit y := ((Prod.isUnit_iff.mpr ⟨x.isUnit, isUnit_one⟩).map e)
  change (DirichletCharacter.changeLevel (Nat.mul_dvd_mul ha hb) χ) y =
    (DirichletCharacter.changeLevel ha (left hab χ)) x
  rw [← hy.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    DirichletCharacter.changeLevel_eq_cast_of_dvd, hy.unit_spec]
  change χ (ZMod.cast y) = χ ((ZMod.chineseRemainder hab).symm (ZMod.cast (x : ZMod m), 1))
  congr 1
  apply (ZMod.chineseRemainder hab).injective
  rw [RingEquiv.apply_symm_apply, cast_crt hab hmn ha hb]
  dsimp [y,e]
  rw [RingEquiv.apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact map_one (ZMod.castHom hb (ZMod b))

theorem right_changeLevel {a b m n : ℕ} [NeZero (m*n)] (hab : a.Coprime b)
    (hmn : m.Coprime n) (ha : a ∣ m) (hb : b ∣ n) (χ : DirichletCharacter ℂ (a*b)) :
    right hmn (DirichletCharacter.changeLevel (Nat.mul_dvd_mul ha hb) χ) =
      DirichletCharacter.changeLevel hb (right hab χ) := by
  ext1 x
  let e := (ZMod.chineseRemainder hmn).symm
  let y := e (1, ↑x)
  have hy : IsUnit y := ((Prod.isUnit_iff.mpr ⟨isUnit_one, x.isUnit⟩).map e)
  change (DirichletCharacter.changeLevel (Nat.mul_dvd_mul ha hb) χ) y =
    (DirichletCharacter.changeLevel hb (right hab χ)) x
  rw [← hy.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    DirichletCharacter.changeLevel_eq_cast_of_dvd, hy.unit_spec]
  change χ (ZMod.cast y) = χ ((ZMod.chineseRemainder hab).symm (1, ZMod.cast (x : ZMod n)))
  congr 1
  apply (ZMod.chineseRemainder hab).injective
  rw [RingEquiv.apply_symm_apply, cast_crt hab hmn ha hb]
  dsimp [y,e]
  rw [RingEquiv.apply_symm_apply]
  apply Prod.ext
  · exact map_one (ZMod.castHom ha (ZMod a))
  · rfl

def prodMul {R S : Type*} [CommRing R] [CommRing S] (f : MulChar R ℂ)
    (g : MulChar S ℂ) : MulChar (R × S) ℂ where
  toFun u := f u.1 * g u.2
  map_one' := by change f 1 * g 1 = 1; simp
  map_mul' x y := by
    change f (x.1*y.1) * g (x.2*y.2) = _
    rw [map_mul, map_mul]
    ring
  map_nonunit' x hx := by
    change f x.1 * g x.2 = 0
    by_cases hl : IsUnit x.1
    · rw [g.map_nonunit (fun hr => hx (Prod.isUnit_iff.mpr ⟨hl,hr⟩)), mul_zero]
    · rw [f.map_nonunit hl, zero_mul]

def join {m n : ℕ} (h : m.Coprime n) (f : DirichletCharacter ℂ m)
    (g : DirichletCharacter ℂ n) : DirichletCharacter ℂ (m*n) :=
  trans (ZMod.chineseRemainder h) (prodMul f g)

theorem left_join {m n : ℕ} (h : m.Coprime n) (f : DirichletCharacter ℂ m)
    (g : DirichletCharacter ℂ n) : left h (join h f g) = f := by
  ext1 x
  change f ((ZMod.chineseRemainder h) ((ZMod.chineseRemainder h).symm (↑x,1))).1 *
    g ((ZMod.chineseRemainder h) ((ZMod.chineseRemainder h).symm (↑x,1))).2 = f x
  simp

theorem right_join {m n : ℕ} (h : m.Coprime n) (f : DirichletCharacter ℂ m)
    (g : DirichletCharacter ℂ n) : right h (join h f g) = g := by
  ext1 x
  change f ((ZMod.chineseRemainder h) ((ZMod.chineseRemainder h).symm (1,↑x))).1 *
    g ((ZMod.chineseRemainder h) ((ZMod.chineseRemainder h).symm (1,↑x))).2 = g x
  simp

theorem determined_by_coordinates {m n : ℕ} (h : m.Coprime n)
    {f g : DirichletCharacter ℂ (m*n)}
    (hl : left h f = left h g) (hr : right h f = right h g) : f = g := by
  ext1 u
  let e := ZMod.chineseRemainder h
  have H (χ : DirichletCharacter ℂ (m*n)) :
      χ (u : ZMod (m*n)) = left h χ (e ↑u).1 * right h χ (e ↑u).2 := by
    have := mulChar_prod (trans e.symm χ) (e ↑u).1 (e ↑u).2
    change χ (e.symm ((e ↑u).1, (e ↑u).2)) = _ at this
    simpa only [Prod.mk.eta, RingEquiv.symm_apply_apply] using this
  rw [H f, H g, hl, hr]

/-- Conductors multiply under the CRT decomposition. -/
theorem conductor_product {m n : ℕ} [NeZero (m*n)] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) :
    (left h χ).conductor * (right h χ).conductor = χ.conductor := by
  let : NeZero m := ⟨left_ne_zero_of_mul (NeZero.ne (m*n))⟩
  let : NeZero n := ⟨right_ne_zero_of_mul (NeZero.ne (m*n))⟩
  let d₁ := (left h χ).conductor
  let d₂ := (right h χ).conductor
  have hd₁ : d₁ ∣ m := (left h χ).conductor_dvd_level
  have hd₂ : d₂ ∣ n := (right h χ).conductor_dvd_level
  apply Nat.dvd_antisymm
  · let d := χ.conductor
    let a := d.gcd m
    let b := d.gcd n
    have ha : a ∣ m := Nat.gcd_dvd_right _ _
    have hb : b ∣ n := Nat.gcd_dvd_right _ _
    have hab : a.Coprime b := h.gcd_both _ _
    have hfact : a*b = d := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr χ.conductor_dvd_level
    have hft : χ.FactorsThrough (a*b) := hfact ▸ χ.factorsThrough_conductor
    obtain ⟨_, η, he⟩ := hft
    have hl : d₁ ∣ a := by
      apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
      rw [he, left_changeLevel hab h ha hb]
      exact DirichletCharacter.changeLevel_factorsThrough _ _
    have hr : d₂ ∣ b := by
      apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
      rw [he, right_changeLevel hab h ha hb]
      exact DirichletCharacter.changeLevel_factorsThrough _ _
    change d₁*d₂ ∣ d
    rw [← hfact]
    exact Nat.mul_dvd_mul hl hr
  · apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
    have h12 : d₁.Coprime d₂ := h.coprime_dvd_left hd₁ |>.coprime_dvd_right hd₂
    let ψ := join h12 (left h χ).primitiveCharacter (right h χ).primitiveCharacter
    refine ⟨Nat.mul_dvd_mul hd₁ hd₂, ψ, determined_by_coordinates h ?_ ?_⟩
    · rw [left_changeLevel h12 h hd₁ hd₂, show left h12 ψ = (left h χ).primitiveCharacter from left_join ..]
      exact (DirichletCharacter.changeLevel_primitiveCharacter _).symm
    · rw [right_changeLevel h12 h hd₁ hd₂, show right h12 ψ = (right h χ).primitiveCharacter from right_join ..]
      exact (DirichletCharacter.changeLevel_primitiveCharacter _).symm

theorem left_conductor_gcd {m n : ℕ} [NeZero (m*n)] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) :
    (left h χ).conductor = χ.conductor.gcd m := by
  rw [← conductor_product h χ, Nat.mul_comm]
  exact (Nat.gcd_mul_of_coprime_of_dvd
    (h.symm.coprime_dvd_left (right h χ).conductor_dvd_level)
    (left h χ).conductor_dvd_level).symm

theorem right_conductor_gcd {m n : ℕ} [NeZero (m*n)] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) :
    (right h χ).conductor = χ.conductor.gcd n := by
  rw [← conductor_product h χ]
  exact (Nat.gcd_mul_of_coprime_of_dvd
    (h.coprime_dvd_left (left h χ).conductor_dvd_level)
    (right h χ).conductor_dvd_level).symm

theorem left_conductor_primePower {p α n : ℕ} [NeZero (p^α*n)] (hp : p.Prime)
    (hα : 0 < α) (h : (p^α).Coprime n) (χ : DirichletCharacter ℂ (p^α*n)) :
    (left h χ).conductor = p^(χ.conductor.factorization p) := by
  let : NeZero (p^α) := ⟨left_ne_zero_of_mul (NeZero.ne (p^α*n))⟩
  let : NeZero n := ⟨right_ne_zero_of_mul (NeZero.ne (p^α*n))⟩
  have hpn : ¬p ∣ n := (hp.coprime_iff_not_dvd).mp ((Nat.coprime_pow_left_iff hα p n).mp h)
  have hz : ((right h χ).conductor).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun H => hpn (H.trans (right h χ).conductor_dvd_level))
  obtain ⟨a,ha,he⟩ := (Nat.dvd_prime_pow hp).mp (left h χ).conductor_dvd_level
  have H : χ.conductor.factorization p = a := by
    rw [← conductor_product h χ, Nat.factorization_mul (left h χ).conductor_ne_zero
      (right h χ).conductor_ne_zero, Finsupp.add_apply, hz, add_zero, he, Nat.factorization_pow_self hp]
  rw [H, he]

/-- Restricting a primitive character of a coprime product to either CRT
factor preserves primitive level. -/
theorem primitive_coordinates {m n : ℕ} [NeZero (m*n)] (h : m.Coprime n)
    {χ : DirichletCharacter ℂ (m*n)} (hχ : χ.IsPrimitive) :
    (left h χ).IsPrimitive ∧ (right h χ).IsPrimitive := by
  change χ.conductor = m*n at hχ
  change (left h χ).conductor = m ∧ (right h χ).conductor = n
  rw [left_conductor_gcd h χ, right_conductor_gcd h χ, hχ,
    Nat.gcd_eq_right (dvd_mul_right _ _), Nat.gcd_eq_right (dvd_mul_left _ _)]
  exact ⟨rfl,rfl⟩

#print axioms primitive_coordinates
#print axioms left_conductor_primePower
#print axioms conductor_product
#print axioms left_changeLevel
#print axioms right_changeLevel
end PintzCRTConductor
