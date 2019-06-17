# W-in-Coq
This is a Coq formalization of Damas-Milner type system and its algorithm W.

Correctness (soundness) and completeness of W have been proved.

This work is strongly based on Catherine Dubois paper "[Certification of a Type Inference Tool for ML: Damas-Milner within Coq](https://link.springer.com/article/10.1023%2FA%3A1006285817788)". But, in contrast, I decided to use LTac automation, dependent types and a modification of "[The Hoare State Monad](https://link.springer.com/chapter/10.1007/978-3-642-03359-9_30)".

Also, this work uses a modified version of the [unification in Coq](https://github.com/rodrigogribeiro/unification) by Rodrigo Ribeiro. More information about his unification in "[A Mechanized Textbook Proof of a Type Unification Algorithm](https://link.springer.com/chapter/10.1007/978-3-319-29473-5_8)".

The extracted code is fully executable and can be found in the src/extraction folder.

To compile the Coq code run `make` in the root folder.

To compile the extraced code run `stack build` in src/extraction folder. 

Note: This is a work in progress! Some parts are still quite messy!

Tested with coq 8.9.0.
