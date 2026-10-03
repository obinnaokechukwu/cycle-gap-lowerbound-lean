# Graphical Balanced Allocation in Lean 4

A Lean 4 / Mathlib formalization of

> Obinna Okechukwu, *Local decisions, diffusive influence, and lower bounds for graphical balanced allocation*, arXiv:2609.38726 [math.PR], 2026. <https://arxiv.org/abs/2609.38726>

```bibtex
@article{okechukwu2026graphical,
  title   = {Local decisions, diffusive influence, and lower bounds for graphical balanced allocation},
  author  = {Okechukwu, Obinna},
  journal = {arXiv preprint arXiv:2609.38726},
  year    = {2026}
}
```

The paper studies graphical two-choice balanced allocation: incoming balls are routed to one endpoint of a uniformly random edge, using rules that decide only from the two endpoint loads. It shows that such endpoint-local rules cannot close load gaps the way global-information strategies can, and makes this precise with diffusive displacement bounds, explicit lower bounds on cycles, cylinders, and tori, a strategy-independent universal lower bound, and matching upper bounds for a smoothed rule compared against a Gaussian free field.

## Build and verify

Install the toolchain named in `lean-toolchain`, with Git available:

```sh
lake update
lake exe cache get
bash scripts/check.sh
```

Lean is pinned to 4.34.1 and Mathlib to `d13f23b723b8a846827a245b89c10fc7d3f11612`; all dependency revisions are recorded in `lake-manifest.json`. Initial dependency and cache retrieval needs network access. If the default cache directory is read-only, set `MATHLIB_CACHE_DIR` to a writable directory.

`scripts/check.sh` builds the library and runs the axiom audit. The audit collects the transitive axioms of every project declaration and fails on any axiom other than `propext`, `Classical.choice`, and `Quot.sound`, or on any unsafe declaration.

## Main entry points

Names below have the prefix `GraphicalAllocation`:

- `Applications.cycle_lower_bound_paper` and `discrete_cycle_lower_bound_paper`: the cycle lower bounds with their exact constants
- `Applications.Graphs.torus_combined_lower_bound`: the combined aspect-ratio and logarithmic torus scale
- `Universal.history_discrete_probability` and `history_continuous_probability`: arbitrary-history strategy lower bounds
- `Probability.bounded_increment_bernstein`: the general martingale inequality on arbitrary probability spaces
- `Smoothed.smoothed_polynomial_expectation_le`: the smoothed rule's general-graph upper bound
- `Smoothed.cycle_smoothed_event_expectation_le`, `cycle_smoothed_continuous_expectation_le`, and `cycle_smoothed_two_sided`: the cutoff `242 log n`, constant `300`, and the two-sided cycle comparison
- `Gaussian.smoothed_gaussian_expectation_le` and `smoothed_gaussian_expectation_absorption`: the Gaussian-field comparison, including an explicit factor `(48ζ + 54)√d log N`

The lower bounds permit arbitrary independent initial laws and extended, possibly infinite expected gaps. The upper bounds start from a constant profile, and their cutoff is chosen for the stated polynomial horizon. The cycle theorem includes zero events and zero physical time in its upper bound.

Continuous time is represented by the exact independent Poisson mixture of event-count laws, with the proved rate-one-per-edge generator. Full-history strategies are represented by their conditional endpoint probabilities; the underlying window estimate holds for every legal allocation of the sampled edge window.

## Layout

- `GraphicalAllocation/`: the proof library, organized by subsystem (`Rules`, `Palm`, `Projections`, `Process`, `Transport`, `Diffusion`, `Geometry`, `Applications`, `Probability`, `Universal`, `Spectral`, `Smoothed`, `Gaussian`)
- `GraphicalAllocation.lean`: the root module that imports the library
- `scripts/check.sh`: build and axiom-audit script
- `scripts/Audit.lean`: the axiom audit over all imported declarations
