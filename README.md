# W-in-Coq
This is a Coq formalization of Damas-Milner type system and it's algorithm W.

So far only correctness have been proved. Completeness is a future work.

This work is strongly based on Catherine Dubois paper "[Certification of a Type Inference Tool for ML: Damas-Milner within Coq](https://link.springer.com/article/10.1023%2FA%3A1006285817788)". But, in contrast, I decided to use LTac automation and dependent types.

Also, I stole the [unification in Coq](https://github.com/rodrigogribeiro/unification) by Rodrigo Ribeiro. So this is a step closer of a fully working extractable code. More information about his unification in "[A Mechanized Textbook Proof of a Type Unification Algorithm](https://link.springer.com/chapter/10.1007/978-3-319-29473-5_8)".

Tested with coq 8.9.0!
