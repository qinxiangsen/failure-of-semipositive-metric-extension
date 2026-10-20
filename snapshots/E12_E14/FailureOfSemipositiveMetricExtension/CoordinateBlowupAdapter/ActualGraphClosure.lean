import FailureOfSemipositiveMetricExtension.CoordinateBlowupAdapter.ActualIncidenceAdapter
import FailureOfSemipositiveMetricExtension.GlobalExceptionalDensity
import FailureOfSemipositiveMetricExtension.GlobalAmbientImmersion

/-! The same actual smooth incidence manifold is exactly the closure of the
explicit four-direction graph away from the paper's four centres. This is a
support/embedded-manifold certificate for the standard reduced graph-closure
model of a disjoint-centre blow-up, NOT a claim that an arbitrary equation
quotient is reduced. -/
namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter.GraphClosure
noncomputable section
open Set
open FailureOfSemipositiveMetricExtension.GlobalIncidence

abbrev Base := PlanePoint × ℂ
def baseAway : Set Base := {q | ∀ r, q.1 ≠ centre r q.2}

/-- The four actual projective directions, restricted to the complement where
all four pairs of homogeneous generators are nonzero. -/
def graph (q : baseAway) : Ambient :=
  (q.val.1,(fun r => chosenDirection q.val.1 r q.val.2),q.val.2)

def graphTotal (q : baseAway) : Total :=
  ⟨graph q, fun r => chosenDirection_incidence q.val.1 r q.val.2⟩

@[simp] theorem graph_base (q : baseAway) : (graph q).1 = q.val.1 := rfl
@[simp] theorem graph_parameter (q : baseAway) : (graph q).2.2 = q.val.2 := rfl

/-- The graph is the rational map given by the SAME four explicit pairs of
linear forms. This includes the moving pair (y-x,z-t*x). -/
theorem graph_direction_formula (q : baseAway) (r : Fin 4) :
    (graph q).2.1 r = Projectivization.mk ℂ (pairMap r q.val.2 q.val.1.rep)
      (fun hz => q.property r ((pairMap_rep_zero_iff q.val.1 r q.val.2).mp hz)) := by
  exact (incidence_unique_away q.val.1 r q.val.2 (q.property r) _).mp
    (chosenDirection_incidence q.val.1 r q.val.2)

theorem graphTotal_away (q : baseAway) : graphTotal q ∈ awayCentres := q.property

/-- No arbitrary graph closure is introduced: its open graph is precisely the
nonexceptional part of the already accepted total space. -/
theorem range_graph_eq_away_image :
    Set.range graph = (Subtype.val : Total → Ambient) '' awayCentres := by
  ext z
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨graphTotal q,graphTotal_away q,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    let q : baseAway := ⟨(blowdown p,projection p),hp⟩
    refine ⟨q,?_⟩
    have heq : graphTotal q = p :=
      unique_away_from_centres (graphTotal q) p rfl rfl (graphTotal_away q)
    exact congrArg Subtype.val heq

/-- Actual ambient closure equality, using the accepted density and closed
embedding. It is stronger than just pointwise satisfaction of equations. -/
theorem closure_graph_eq_actual_total : closure (Set.range graph) = totalLocus := by
  rw [range_graph_eq_away_image, total_inclusion_isClosedEmbedding.closure_image_eq,
    awayCentres_dense.closure_eq, Set.image_univ]
  ext q
  exact ⟨fun ⟨p,hp⟩ => hp ▸ p.property, fun hq => ⟨⟨q,hq⟩,rfl⟩⟩

/-- This comparison uses the identity of ambient points, so both inverse maps,
the plane blowdown, the parameter and all four directions are preserved. -/
def actualGraphClosureHomeomorph : {q : Ambient // q ∈ closure (Set.range graph)} ≃ₜ Total :=
  Homeomorph.setCongr closure_graph_eq_actual_total

@[simp] theorem actualGraphClosureHomeomorph_val
    (q : {q : Ambient // q ∈ closure (Set.range graph)}) :
    (actualGraphClosureHomeomorph q).val = q.val := rfl

@[simp] theorem actualGraphClosureHomeomorph_blowdown
    (q : {q : Ambient // q ∈ closure (Set.range graph)}) :
    blowdown (actualGraphClosureHomeomorph q) = q.val.1 := rfl

@[simp] theorem actualGraphClosureHomeomorph_parameter
    (q : {q : Ambient // q ∈ closure (Set.range graph)}) :
    projection (actualGraphClosureHomeomorph q) = q.val.2.2 := rfl

@[simp] theorem actualGraphClosureHomeomorph_directions
    (q : {q : Ambient // q ∈ closure (Set.range graph)}) :
    directions (actualGraphClosureHomeomorph q) = q.val.2.1 := rfl

/-- The four base loci are literally the paper's four distinct centres. -/
theorem graph_generators_base_loci (p : PlanePoint) (t : ℂ) (r : Fin 4) :
    pairMap r t p.rep = 0 ↔ p = centre r t := pairMap_rep_zero_iff p r t

theorem graph_centres_disjoint (t : ℂ) : Function.Injective (fun r => centre r t) :=
  centre_injective t

end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter.GraphClosure
