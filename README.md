# EilenbergSteenrodAxioms

This repository contains a formalization of the Eilenberg-Steenrod axioms for a homology theory in the Lean theorem prover.

## File Summaries

*   **`EilenbergSteenrodAxioms/TopologicalPair.lean`**: Defines the category of topological pairs `TopPair`, whose objects are pairs `(X, A)` where `X` is a topological space and `A` is a subset of `X`. It also defines morphisms between these pairs and establishes the category structure.
*   **`EilenbergSteenrodAxioms/AlgebraicMayerVietoris.lean`**: Develops the algebraic machinery for the Mayer-Vietoris sequence. It proves that given a specific diagram of objects and morphisms in an abelian category (fulfilling certain exactness and commutativity conditions), a long exact sequence can be constructed. This is a key algebraic component for proving the Mayer-Vietoris sequence for homology theories.
*   **`EilenbergSteenrodAxioms/EilenbergSteenrodAxioms.lean`**: This file defines the Eilenberg-Steenrod axioms for a homology theory on the category of topological pairs. It constructs the Mayer-Vietoris long exact sequence for any theory satisfying these axioms.
*   **`EilenbergSteenrodAxioms/Homology.lean`**: This file defines a functor from the category of topological spaces `TopCat` to `TopPair` by sending a topological space `X` to the pair `(X, ∅)`. This is used to pull back an Eilenberg-Steenrod homology theory on `TopPair` to a homology theory on `TopCat`. It also reformulates the Mayer-Vietoris sequence for topological spaces.
