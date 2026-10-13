import D2RelationGap.MappedCap

/-!
Finite contextual local schedules for the actual path-move derivations.
OpenAI, "A Counterexample to Wall's D(2) Problem" (October 6, 2026),
openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/, supplies the
underlying obstruction. This is a TARGET schedule, not a source-lifting theorem.
-/
noncomputable section
namespace D2RelationGap.MoveSchedule
open OrientedSimplices SimplicialTransport EdgePaths BasedLoops
variable {V : Type*} [LinearOrder V] {A : PreAbstractSimplicialComplex V}

/-- One primitive move under an actual prefix and suffix, in either direction. -/
inductive Local : {x y : V} → Path A x y → Path A x y → Type _
  | stutter {x u y} (pre : Path A x u) (hu : ({u} : Finset V) ∈ A) (post : Path A u y) :
      Local (append pre (.cons (by simpa using hu) post)) (append pre post)
  | backtrack {x u v y} (pre : Path A x u) (huv : ({u,v} : Finset V) ∈ A) (post : Path A u y) :
      Local (append pre (.cons huv (.cons (by simpa [Finset.pair_comm] using huv) post))) (append pre post)
  | triangle {x u v w y} (pre : Path A x u) (ht : ({u,v,w} : Finset V) ∈ A) (post : Path A w y) :
      Local (append pre (.cons (pair_mem_of_face A _ ht u v (by simp) (by simp))
        (.cons (pair_mem_of_face A _ ht v w (by simp) (by simp)) post)))
        (append pre (.cons (pair_mem_of_face A _ ht u w (by simp) (by simp)) post))
  | symm {x y} {p q : Path A x y} : Local p q → Local q p

def localMoves {x y : V} {p q : Path A x y} (m : Local p q) : Moves p q := by
  induction m with
  | stutter pre hu post => exact prefixMoves pre (.stutter hu post)
  | backtrack pre h post => exact prefixMoves pre (.backtrack h post)
  | triangle pre h post => exact prefixMoves pre (.triangle h post)
  | symm m ih => exact .symm ih

def localPrefix {x y z : V} (pre : Path A x y) {p q : Path A y z} (m : Local p q) :
    Local (append pre p) (append pre q) := by
  induction m with
  | stutter pre' h post => simpa only [append_assoc] using Local.stutter (append pre pre') h post
  | backtrack pre' h post => simpa only [append_assoc] using Local.backtrack (append pre pre') h post
  | triangle pre' h post => simpa only [append_assoc] using Local.triangle (append pre pre') h post
  | symm m ih => exact .symm ih

def localSuffix {x y z : V} {p q : Path A x y} (m : Local p q) (post : Path A y z) :
    Local (append p post) (append q post) := by
  induction m with
  | stutter pre h post' => simpa only [append_assoc,append] using Local.stutter pre h (append post' post)
  | backtrack pre h post' => simpa only [append_assoc,append] using Local.backtrack pre h (append post' post)
  | triangle pre h post' => simpa only [append_assoc,append] using Local.triangle pre h (append post' post)
  | symm m ih => exact .symm (ih post)

/-- A literal finite list of composable local operations with fixed endpoints. -/
inductive Schedule {x y : V} : Path A x y → Path A x y → Type _
  | nil (p : Path A x y) : Schedule p p
  | cons {p q r : Path A x y} : Local p q → Schedule q r → Schedule p r

def concatenate {x y : V} {p q r : Path A x y} (m : Schedule p q) (n : Schedule q r) : Schedule p r := by
  induction m with
  | nil => exact n
  | cons h m ih => exact .cons h (ih n)

def reverseSchedule {x y : V} {p q : Path A x y} (m : Schedule p q) : Schedule q p := by
  induction m with
  | nil => exact .nil _
  | cons h m ih => exact concatenate ih (.cons (.symm h) (.nil _))

def prefixSchedule {x y z : V} (pre : Path A x y) {p q : Path A y z} (m : Schedule p q) :
    Schedule (append pre p) (append pre q) := by
  induction m with
  | nil => exact .nil _
  | cons h m ih => exact .cons (localPrefix pre h) ih

def suffixSchedule {x y z : V} {p q : Path A x y} (m : Schedule p q) (post : Path A y z) :
    Schedule (append p post) (append q post) := by
  induction m with
  | nil => exact .nil _
  | cons h m ih => exact .cons (localSuffix h post) ih

def movesOfSchedule {x y : V} {p q : Path A x y} (m : Schedule p q) : Moves p q := by
  induction m with
  | nil => exact .refl _
  | cons h m ih => exact .trans (localMoves h) ih

/-- Normalize every TYPE-valued finite derivation without an equality oracle. -/
def scheduleOfMoves {x y : V} {p q : Path A x y} (m : Moves p q) : Schedule p q := by
  induction m with
  | refl p => exact .nil p
  | symm m ih => exact reverseSchedule ih
  | trans m n ih jh => exact concatenate ih jh
  | stutter h p => exact .cons (Local.stutter (.refl _ h) h p) (.nil p)
  | backtrack h p => exact .cons (Local.backtrack (.refl _ (startActive p)) h p) (.nil p)
  | @triangle u v w z h p =>
    let e := Local.triangle (u := u) (v := v) (w := w)
      (.refl u (vertex_mem_of_face A _ h u (by simp))) h p
    simpa only [append] using Schedule.cons e (Schedule.nil _)
  | prepend h m ih => exact prefixSchedule (single h) ih
  | suffix r m ih => exact suffixSchedule ih r

def size {x y : V} {p q : Path A x y} : Schedule p q → ℕ
  | .nil _ => 0
  | .cons _ m => size m + 1

theorem size_concatenate {x y : V} {p q r : Path A x y} (m : Schedule p q) (n : Schedule q r) :
    size (concatenate m n) = size m + size n := by
  induction m with
  | nil => simp [concatenate,size]
  | cons h m ih =>
    change size (concatenate m n) + 1 = (size m + 1) + size n
    rw [ih n]
    omega

theorem size_reverse {x y : V} {p q : Path A x y} (m : Schedule p q) : size (reverseSchedule m) = size m := by
  induction m with
  | nil => rfl
  | cons h m ih =>
    change size (concatenate (reverseSchedule m) (.cons (.symm h) (.nil _))) = size m + 1
    rw [size_concatenate,ih]
    rfl

theorem size_prefix {x y z : V} (pre : Path A x y) {p q : Path A y z} (m : Schedule p q) :
    size (prefixSchedule pre m) = size m := by induction m <;> simp_all [prefixSchedule,size]

theorem size_suffix {x y z : V} {p q : Path A x y} (m : Schedule p q) (post : Path A y z) :
    size (suffixSchedule m post) = size m := by induction m <;> simp_all [suffixSchedule,size]

def primitiveCount {x y : V} {p q : Path A x y} : Moves p q → ℕ
  | .refl _ => 0
  | .symm m => primitiveCount m
  | .trans m n => primitiveCount m + primitiveCount n
  | .stutter _ _ => 1
  | .backtrack _ _ => 1
  | .triangle _ _ => 1
  | .prepend _ m => primitiveCount m
  | .suffix _ m => primitiveCount m

theorem schedule_size {x y : V} {p q : Path A x y} (m : Moves p q) :
    size (scheduleOfMoves m) = primitiveCount m := by
  induction m with
  | prepend h m ih =>
    change size (prefixSchedule (single h) (scheduleOfMoves m)) = primitiveCount m
    rw [size_prefix,ih]
  | refl => rfl
  | stutter => rfl
  | backtrack => rfl
  | triangle => rfl
  | symm m ih => change size (reverseSchedule (scheduleOfMoves m)) = _; rw [size_reverse,ih]; rfl
  | trans m n ih jh => change size (concatenate (scheduleOfMoves m) (scheduleOfMoves n)) = _; rw [size_concatenate,ih,jh]; rfl
  | suffix r m ih => change size (suffixSchedule (scheduleOfMoves m) r) = _; rw [size_suffix,ih]; rfl

theorem schedule_iff_moves {x y : V} (p q : Path A x y) : Nonempty (Schedule p q) ↔ Nonempty (Moves p q) :=
  ⟨fun ⟨m⟩ => ⟨movesOfSchedule m⟩,fun ⟨m⟩ => ⟨scheduleOfMoves m⟩⟩

theorem schedule_iff_class_eq {x y : V} (p q : Path A x y) :
    Nonempty (Schedule p q) ↔ Quotient.mk (pathSetoid A x y) p = Quotient.mk _ q :=
  (schedule_iff_moves p q).trans (class_eq_iff_moves p q).symm

section Maps
variable {W : Type*} [LinearOrder W] {B : PreAbstractSimplicialComplex W}

def mapLocal (f : V → W) (hf : A.map f ≤ B) {x y : V} {p q : Path A x y} (m : Local p q) :
    Local (mapPath f hf p) (mapPath f hf q) := by
  induction m with
  | @stutter u y pre h post =>
    have hh : ({f u} : Finset W) ∈ B := by simpa using image_mem f hf _ h
    simpa only [mapPath_append,mapPath] using Local.stutter (mapPath f hf pre) hh (mapPath f hf post)
  | @backtrack u v y pre h post =>
    have hh : ({f u,f v} : Finset W) ∈ B := by simpa using image_mem f hf _ h
    simpa only [mapPath_append,mapPath] using Local.backtrack (mapPath f hf pre) hh (mapPath f hf post)
  | @triangle u v w y pre h post =>
    have hh : ({f u,f v,f w} : Finset W) ∈ B := by simpa using image_mem f hf _ h
    simpa only [mapPath_append,mapPath] using Local.triangle (mapPath f hf pre) hh (mapPath f hf post)
  | symm m ih => exact .symm ih

def mapSchedule (f : V → W) (hf : A.map f ≤ B) {x y : V} {p q : Path A x y} (m : Schedule p q) :
    Schedule (mapPath f hf p) (mapPath f hf q) := by
  induction m with
  | nil => exact .nil _
  | cons h m ih => exact .cons (mapLocal f hf h) ih

theorem size_mapSchedule (f : V → W) (hf : A.map f ≤ B) {x y : V} {p q : Path A x y}
    (m : Schedule p q) : size (mapSchedule f hf m) = size m := by
  induction m with
  | nil => rfl
  | cons h m ih => change size (mapSchedule f hf m) + 1 = size m + 1; rw [ih]

end Maps

theorem scheduled_triangle_square_count : size (scheduleOfMoves SourceRefinement.trianglePath_square) = 4 := by
  rw [schedule_size]
  rfl

theorem omitted_primitive_operations_rejected : size (scheduleOfMoves SourceRefinement.trianglePath_square) ≠ 0 := by
  rw [scheduled_triangle_square_count]
  decide

theorem nonexistent_triangle_schedule_rejected :
    ¬ Nonempty (Schedule cycleLoop (.refl 0 cycleBase.property)) :=
  fun h => nonexistent_triangle_shortcut_rejected ((schedule_iff_moves _ _).mp h)

theorem one_holonomy_value_is_not_schedule_adequacy :
    value cycleTransport (append cycleLoop cycleLoop) = value cycleTransport (.refl 0 cycleBase.property) ∧
    ¬ Nonempty (Schedule (append cycleLoop cycleLoop) (.refl 0 cycleBase.property)) :=
  ⟨SourceRefinement.equal_unit_value_is_not_move_adequacy.1,
    fun h => SourceRefinement.equal_unit_value_is_not_move_adequacy.2 ((schedule_iff_moves _ _).mp h)⟩

end D2RelationGap.MoveSchedule
