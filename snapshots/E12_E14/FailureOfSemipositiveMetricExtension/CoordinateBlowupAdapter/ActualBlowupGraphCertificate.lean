import FailureOfSemipositiveMetricExtension.CoordinateBlowupAdapter.ActualGraphClosure
import FailureOfSemipositiveMetricExtension.CoordinateBlowupAdapter.PreferredCoordinateChange

namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter.GraphClosure
noncomputable section
open Set
open FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff

open scoped BigOperators

theorem totalCentreIdeal_eq_product (R : Type*) [CommRing R] (t : R) (a : Fin 3) :
    totalCentreIdeal R t a = ∏ r : Fin 4, normalizedCentreIdeal R t a r := by
  classical
  have hall (S : Finset (Fin 4)) :
      (∏ r ∈ S, normalizedCentreIdeal R t a r) = S.inf (normalizedCentreIdeal R t a) := by
    induction S using Finset.induction_on with
    | empty => simp [Ideal.one_eq_top]
    | @insert r S hr ih =>
      rw [Finset.prod_insert hr, Finset.inf_insert, ← ih]
      apply Ideal.mul_eq_inf_of_coprime
      apply Ideal.sup_prod_eq_top
      intro s hs
      apply normalizedCentreIdeal_pairwise R t a r s
      intro h
      exact hr (h ▸ hs)
  simpa only [Finset.mem_univ, Finset.inf_univ_eq_iInf,
    totalCentreIdeal] using (hall Finset.univ).symm

/-- All paper-specific premises for the standard disjoint-centre reduced
blow-up graph-closure identification. The actual source is the already accepted
complex manifold, with its actual holomorphic CLOSED embedding and injective
tangent map. Thus reduced analytic-subspace uniqueness applies; the certificate
does not infer reducedness of the unreduced raw equation scheme from its points. -/
structure ActualBlowupGraphCertificate : Prop where
  closure_identity : closure (Set.range graph) = totalLocus
  closed_embedding : Topology.IsClosedEmbedding (fun p : Total => p.val)
  analytic_embedding : ContMDiff 𝓘(ℂ,ChartCoord) ambientModel ω (fun p : Total => p.val)
  injective_tangent : ∀ p : Total, Function.Injective
    (mfderiv 𝓘(ℂ,ChartCoord) ambientModel (fun p : Total => p.val) p)
  graph_directions : ∀ (q : baseAway) (r : Fin 4),
    (graph q).2.1 r = Projectivization.mk ℂ (pairMap r q.val.2 q.val.1.rep)
      (fun hz => q.property r ((pairMap_rep_zero_iff q.val.1 r q.val.2).mp hz))
  centres_disjoint : ∀ t : ℂ, Function.Injective (fun r => centre r t)
  pair_equations : ∀ r b,
    rawPair (Polynomial ℂ) Polynomial.X r b =
      FailureOfSemipositiveMetricExtension.GlobalIncidence.IncidenceEquations.linearPair r b
  pair_evaluation : ∀ (t : ℂ) (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ) (r : Fin 4) (b : Fin 2),
    FailureOfSemipositiveMetricExtension.GlobalIncidence.IncidenceEquations.evaluate t v w
      (FailureOfSemipositiveMetricExtension.GlobalIncidence.IncidenceEquations.linearPair r b) = pairMap r t v b
  scheme_union_is_product : ∀ a : Fin 3,
    totalCentreIdeal (Polynomial ℂ) Polynomial.X a =
      ∏ r : Fin 4, normalizedCentreIdeal (Polynomial ℂ) Polynomial.X a r
  scheme_centres_comaximal : ∀ (a : Fin 3) (r s : Fin 4), r ≠ s →
    normalizedCentreIdeal (Polynomial ℂ) Polynomial.X a r ⊔
      normalizedCentreIdeal (Polynomial ℂ) Polynomial.X a s = ⊤
  centre_coordinate_ideals : ∀ r,
    (pairIdeal (MvPolynomial.X 0 : PairPolynomial (Polynomial ℂ)) (MvPolynomial.X 1)).map
      (preferredCoordinateEquiv (Polynomial ℂ) Polynomial.X r).toRingHom =
      normalizedCentreIdeal (Polynomial ℂ) Polynomial.X (preferredCentreChart r) r
  centre_preferred_cover : ∀ (a : Fin 3) (r : Fin 4),
    normalizedCentreIdeal (Polynomial ℂ) Polynomial.X a r ⊔
      Ideal.span {normalizedVector (Polynomial ℂ) a (preferredCentreChart r)} = ⊤

/-- The actual instance, not a new axiom asserting a blow-up conclusion. Every
field is discharged by accepted actual-object facts or the new coordinate proof. -/
theorem actual_blowup_graph_certificate : ActualBlowupGraphCertificate where
  closure_identity := closure_graph_eq_actual_total
  closed_embedding := total_analytic_closed_immersion.1
  analytic_embedding := total_analytic_closed_immersion.2.1
  injective_tangent := total_analytic_closed_immersion.2.2
  graph_directions := graph_direction_formula
  centres_disjoint := graph_centres_disjoint
  pair_equations := Paper.rawPair_eq_original
  pair_evaluation := FailureOfSemipositiveMetricExtension.GlobalIncidence.IncidenceEquations.evaluate_linearPair
  scheme_union_is_product := totalCentreIdeal_eq_product (Polynomial ℂ) Polynomial.X
  scheme_centres_comaximal := normalizedCentreIdeal_pairwise (Polynomial ℂ) Polynomial.X
  centre_coordinate_ideals := preferredCoordinateEquiv_centre_ideal (Polynomial ℂ) Polynomial.X
  centre_preferred_cover := normalizedCentre_preferred_comaximal (Polynomial ℂ) Polynomial.X

end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter.GraphClosure
