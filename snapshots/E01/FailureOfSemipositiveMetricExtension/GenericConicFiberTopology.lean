import FailureOfSemipositiveMetricExtension.GenericConicFiber

/-! The entire actual generic pencil fibre, with its inherited subtype topology,
is homeomorphic to the actual compact Hausdorff projective line. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set Topology
open scoped Manifold ContDiff

def PencilFiber (c : Data) := {p : Fiber c.t // pencilMap c.t p = pencilValue c}

instance instTopologicalSpacePencilFiber (c : Data) : TopologicalSpace (PencilFiber c) :=
  inferInstanceAs (TopologicalSpace {p : Fiber c.t // pencilMap c.t p = pencilValue c})

theorem pencilFiber_topology_is_subspace (c : Data) : instTopologicalSpacePencilFiber c =
    TopologicalSpace.induced (fun p : PencilFiber c => p.val) (inferInstance : TopologicalSpace (Fiber c.t)) := rfl

def fiberParam (c : Data) (d : Direction) : PencilFiber c := ⟨param c d,pencilMap_param c d⟩

def fiberInverse (c : Data) (p : PencilFiber c) : Direction := FixedFiber.direction c.t 3 p.val

@[simp] theorem fiberInverse_param (c : Data) (d : Direction) : fiberInverse c (fiberParam c d) = d :=
  param_direction_three c d

@[simp] theorem fiberParam_inverse (c : Data) (p : PencilFiber c) : fiberParam c (fiberInverse c p) = p := by
  apply Subtype.ext
  change param c (FixedFiber.direction c.t 3 p.val) = p.val
  have hp : p.val ∈ Set.range (param c) := (Set.ext_iff.mp (range_param c) p.val).mpr p.property
  obtain ⟨d,hd⟩ := hp
  rw [← hd,param_direction_three]

def fiberEquiv (c : Data) : Direction ≃ PencilFiber c where
  toFun := fiberParam c
  invFun := fiberInverse c
  left_inv := fiberInverse_param c
  right_inv := fiberParam_inverse c

theorem fiberParam_continuous (c : Data) : Continuous (fiberParam c) :=
  (param_contMDiff c 0).continuous.subtype_mk _

theorem fiberInverse_continuous (c : Data) : Continuous (fiberInverse c) :=
  (FixedFiber.direction_contMDiff c.t 3 0).continuous.comp continuous_subtype_val

def fiberHomeomorph (c : Data) : Direction ≃ₜ PencilFiber c where
  toEquiv := fiberEquiv c
  continuous_toFun := fiberParam_continuous c
  continuous_invFun := fiberInverse_continuous c

theorem pencilFiber_isClosed (c : Data) : IsClosed {p : Fiber c.t | pencilMap c.t p = pencilValue c} :=
  isClosed_eq (pencilMap_continuous c.t c.t_ne_zero) continuous_const

instance instCompactSpacePencilFiber (c : Data) : CompactSpace (PencilFiber c) :=
  isCompact_iff_compactSpace.mp (pencilFiber_isClosed c).isCompact

instance instT2SpacePencilFiber (c : Data) : T2Space (PencilFiber c) :=
  inferInstanceAs (T2Space {p : Fiber c.t // pencilMap c.t p = pencilValue c})

instance instSecondCountableTopologyPencilFiber (c : Data) : SecondCountableTopology (PencilFiber c) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
