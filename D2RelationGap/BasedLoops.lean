import D2RelationGap.EdgePaths

/-!
The based-loop GROUP of actual finite paths modulo the checked finite moves.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying construction and obstruction. Presentation/original-G/pi1 adequacy
remains open; no relation-gap theorem is asserted.
-/
noncomputable section
namespace D2RelationGap.BasedLoops
open OrientedSimplices SimplicialTransport EdgePaths
variable {V K : Type*} [LinearOrder V] [Field K]

theorem startActive {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    ({u} : Finset V) ∈ A := by
  cases p with
  | refl u hu => exact hu
  | cons h p => exact vertex_mem_of_face A _ h _ (by simp)

theorem endActive {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    ({v} : Finset V) ∈ A := by
  induction p with
  | refl u hu => exact hu
  | cons h p ih => exact ih

def single {A : PreAbstractSimplicialComplex V} {u v : V}
    (h : ({u, v} : Finset V) ∈ A) : Path A u v :=
  .cons h (.refl v (vertex_mem_of_face A _ h v (by simp)))

def reverse {A : PreAbstractSimplicialComplex V} {u v : V} : Path A u v → Path A v u
  | .refl u hu => .refl u hu
  | .cons h p => append (reverse p) (single (by simpa [Finset.pair_comm] using h))

theorem append_assoc {A : PreAbstractSimplicialComplex V} {u v w z : V}
    (p : Path A u v) (q : Path A v w) (r : Path A w z) :
    append (append p q) r = append p (append q r) := by
  induction p with
  | refl => rfl
  | cons h p ih => simp [append, ih]

theorem append_right_refl {A : PreAbstractSimplicialComplex V} {u v : V}
    (p : Path A u v) (hv : ({v} : Finset V) ∈ A) : append p (.refl v hv) = p := by
  induction p with
  | refl => rfl
  | cons h p ih => simp [append, ih]

def prefixMoves {A : PreAbstractSimplicialComplex V} {u v w : V}
    (p : Path A u v) {q r : Path A v w} (m : Moves q r) :
    Moves (append p q) (append p r) := by
  induction p with
  | refl => exact m
  | cons h p ih => exact .prepend h (ih m)

/-- Cancellation is built from actual backtracking derivations. -/
def reverse_right_cancel {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    Moves (append p (reverse p)) (.refl u (startActive p)) := by
  induction p with
  | refl => exact .refl _
  | @cons u v w h p ih =>
    change Moves (.cons h (append p (append (reverse p)
      (single (by simpa [Finset.pair_comm] using h))))) _
    rw [← append_assoc]
    exact .trans (.prepend h (.suffix _ ih)) (.backtrack h (.refl u (startActive (.cons h p))))

def reverse_left_cancel {A : PreAbstractSimplicialComplex V} {u v : V} (p : Path A u v) :
    Moves (append (reverse p) p) (.refl v (endActive p)) := by
  induction p with
  | refl => exact .refl _
  | @cons u v w h p ih =>
    change Moves (append (append (reverse p) (single (by simpa [Finset.pair_comm] using h)))
      (.cons h p)) _
    rw [append_assoc]
    exact .trans (prefixMoves (reverse p)
      (.backtrack (by simpa [Finset.pair_comm] using h) p)) ih

/-- Composition on the existing path quotient, with both well-definedness proofs. -/
def compose {A : PreAbstractSimplicialComplex V} {u v w : V} :
    PathClass A u v → PathClass A v w → PathClass A u w :=
  Quotient.lift₂ (fun p q => Quotient.mk _ (append p q)) (by
    intro p q p' q' ⟨m⟩ ⟨n⟩
    exact Quotient.sound ⟨Moves.trans (Moves.suffix q m) (prefixMoves p' n)⟩)

theorem compose_mk {A : PreAbstractSimplicialComplex V} {u v w : V}
    (p : Path A u v) (q : Path A v w) :
    compose (Quotient.mk _ p) (Quotient.mk _ q) = Quotient.mk _ (append p q) := rfl

abbrev Loop (A : PreAbstractSimplicialComplex V) (u : Vertex A) := PathClass A u.val u.val

instance loopMonoid (A : PreAbstractSimplicialComplex V) (u : Vertex A) : Monoid (Loop A u) where
  mul := compose
  one := Quotient.mk _ (.refl u.val u.property)
  mul_assoc a b c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro p q r
    exact congrArg (Quotient.mk _) (append_assoc p q r)
  one_mul a := by
    refine Quotient.inductionOn a ?_
    intro p
    rfl
  mul_one a := by
    refine Quotient.inductionOn a ?_
    intro p
    exact congrArg (Quotient.mk _) (append_right_refl p u.property)

theorem reverse_class_left_cancel {A : PreAbstractSimplicialComplex V} (u : Vertex A)
    (p : Path A u.val u.val) :
    (Quotient.mk _ (reverse p) : Loop A u) * Quotient.mk _ p = 1 :=
  Quotient.sound ⟨reverse_left_cancel p⟩

theorem reverse_class_right_cancel {A : PreAbstractSimplicialComplex V} (u : Vertex A)
    (p : Path A u.val u.val) :
    (Quotient.mk _ p : Loop A u) * Quotient.mk _ (reverse p) = 1 :=
  Quotient.sound ⟨reverse_right_cancel p⟩

/-- Well-definedness of reversal uses actual cancellation and inverse uniqueness
in this monoid; it does not postulate compatibility with the move relation. -/
def inverse {A : PreAbstractSimplicialComplex V} (u : Vertex A) : Loop A u → Loop A u :=
  Quotient.lift (fun p => Quotient.mk _ (reverse p)) (by
    intro p q he
    have hpq : (Quotient.mk _ p : Loop A u) = Quotient.mk _ q := Quotient.sound he
    apply left_inv_eq_right_inv
    · exact reverse_class_left_cancel u p
    · rw [hpq]
      exact reverse_class_right_cancel u q)

instance loopGroup (A : PreAbstractSimplicialComplex V) (u : Vertex A) : Group (Loop A u) where
  __ := loopMonoid A u
  inv := inverse u
  inv_mul_cancel a := by
    refine Quotient.inductionOn a ?_
    intro p
    exact reverse_class_left_cancel u p

/-- A genuine group-domain monoid homomorphism from supplied flat transport. -/
def holonomy {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A) (u : Vertex A) :
    Loop A u →* Kˣ where
  toFun := classValue tau
  map_one' := rfl
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    exact value_append tau p q

theorem holonomy_mk {A : PreAbstractSimplicialComplex V} (tau : Transport (K := K) A)
    (u : Vertex A) (p : Path A u.val u.val) : holonomy tau u (Quotient.mk _ p) = value tau p := rfl



theorem null_iff_finite_moves {A : PreAbstractSimplicialComplex V} (u : Vertex A)
    (p : Path A u.val u.val) : (Quotient.mk _ p : Loop A u) = 1 ↔
      Nonempty (Moves p (.refl u.val u.property)) := class_eq_iff_moves p _

section Maps
variable {U : Type*} [LinearOrder U]
def map {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (f : U → V) (hf : A.map f ≤ B) (u : Vertex A) : Loop A u →* Loop B (mapVertex f hf u) where
  toFun := mapClass f hf
  map_one' := rfl
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    exact congrArg (Quotient.mk _) (mapPath_append f hf p q)

theorem holonomy_natural {A : PreAbstractSimplicialComplex U} {B : PreAbstractSimplicialComplex V}
    (tau : Transport (K := K) B) (f : U → V) (hf : A.map f ≤ B) (u : Vertex A) :
    (holonomy tau (mapVertex f hf u)).comp (map f hf u) = holonomy (pullback tau f hf) u := by
  apply MonoidHom.ext
  intro c
  exact classValue_mapClass tau f hf c
end Maps

def cycleBase : Vertex cycleComplex :=
  ⟨0, by change ({0} : Finset (Fin 3)).Nonempty ∧ _; decide⟩

theorem cycle_class_nonidentity : (Quotient.mk _ cycleLoop : Loop cycleComplex cycleBase) ≠ 1 := by
  intro he
  exact nonexistent_triangle_shortcut_rejected ((null_iff_finite_moves cycleBase cycleLoop).mp he)

/-- Unlike the sign witness, this transport distinguishes a loop from its inverse. -/
def scaledCycleTransport (q : ℚˣ) : Transport (K := ℚ) cycleComplex where
  unit u v := if u = 0 ∧ v = 2 then q⁻¹ else if u = 2 ∧ v = 0 then q else 1
  flat := by
    intro u v w h
    change ({u, v, w} : Finset (Fin 3)).Nonempty ∧ ({u, v, w} : Finset (Fin 3)).card ≤ 2 at h
    fin_cases u <;> fin_cases v <;> fin_cases w <;> simp_all

theorem scaled_cycle_holonomy (q : ℚˣ) :
    holonomy (scaledCycleTransport q) cycleBase (Quotient.mk _ cycleLoop) = q := by
  change value (scaledCycleTransport q) cycleLoop = q
  simp [value, scaledCycleTransport, cycleLoop]

theorem unreversed_inverse_rejected :
    (Quotient.mk _ cycleLoop : Loop cycleComplex cycleBase)⁻¹ ≠ Quotient.mk _ cycleLoop := by
  intro he
  let q : ℚˣ := Units.mk0 2 (by norm_num)
  let phi := holonomy (scaledCycleTransport q) cycleBase
  have hv : phi (Quotient.mk _ cycleLoop) = q := scaled_cycle_holonomy q
  have hi : (phi (Quotient.mk _ cycleLoop))⁻¹ = phi (Quotient.mk _ cycleLoop) :=
    (map_inv phi _).symm.trans (congrArg phi he)
  have hh : q⁻¹ = q :=
    (congrArg (fun x : ℚˣ => x⁻¹) hv).symm.trans (hi.trans hv)
  have hc := congrArg (fun x : ℚˣ => (x : ℚ)) hh
  norm_num [q] at hc

end D2RelationGap.BasedLoops
