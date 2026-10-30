# Smooth tight nonrigidity

| Content | Location |
|---|---|
| Current manuscript, ver614 published as ver1030, and arXiv source package | [ver1030](paper/ver1030/README.md) |
| Earlier manuscript, ver507, and arXiv submission package | [ver1011](paper/ver1011/README.md) |
| Original illustrated manuscript and figures | [ver1009](paper/ver1009/README.md) |
| Latest integrated Lean sources and exact proof status | [lean](lean/README.md) |
| Formalized results and contributions to Lean | [formalization report](lean/formalization-report.md) |
| Reusable entry points across mathematics | [library catalog](lean/TightVer401/Library/README.md) |
| Interactive numerical geometry and illustrated construction | [visualization](visualization/README.md) |

The current paper, **Isometric tight tori with different enclosed volumes**, is [ver1030](paper/ver1030/README.md), the unchanged local ver614 manuscript dated October 30, 2026. It uses a closed asymptotic curve from the annulus of Banks, Ghomi, Qiu, and Raffaelli, a shorter geometric tight-torus completion using BGQR's curvature argument and Gauss--Bonnet, and a supported infinitesimal bending with nonzero normal flux. The package includes the PDF, LaTeX source, arXiv source archive, and 14 passing exact algebra and source-consistency checks. These checks do not certify the global proof.

The existing Lean audit concerns the frozen ver503 manuscript in [ver1009](paper/ver1009/README.md), and is not an audit of ver1030. For that earlier route, Lean proves the **first noncongruent isometric tight-torus pair unconditionally**, including a common smooth positive metric, nonempty open agreement and no open planar patch. Its source-bound audit passed with no admissions or custom axioms. Full-manuscript formalization remains **incomplete**, with Cantor-family and extension applications deferred. The numerical meshes illustrate the construction and do not certify it.

To explore the visualization, serve this repository root:

```sh
python -m http.server 8000 --bind 127.0.0.1
```

Then open **http://127.0.0.1:8000/visualization/index.html**. Detailed build and usage instructions are in each directory's README.

## AI usage and my personal words

This paper is written "assisted" by (in fact JUST BY) ChatGPT-5.6-Sol, ChatGPT-6-Astra and ChatGPT-6.1-Sol. 

I do not claim the correctness of this paper yet. This has passed the check of AI in various different versions, and none found any fatal errors, and this is all I can now give (20261009). I'm still working on the human checking and formalization. About the credit, you can read my story and decide for yourself.

Edit 20261010: I now DO claim the correctness of the paper because the most important theorem compiles without sorry or extra axiom. (Details see the directory) Yet the risks are: 
1. I only falsified the rigidity conjecture, but didn't do the other propositions like the cantor family. 
2. The theorem translation might not be 100% risk-free. AI has checked it and it's highly unlikely that it tricks us, but you can never be sure.
3. Mistranslations might happen during the process and the manuscript's lemmas and exact proof details might not be 100% correct. The formalization guarantees the existence of the band and the existence of the counterexample, but all the other steps might not be accurately resembled. In fact the manuscript will go through many edits after the formalization, and those edits might deviate more from the formalization's route. (In fact this face the same problem as the NS equation proof) Yet if we treat natural language manuscripts as sketches and roadmaps, its guiding a correct lean proof already guarantees its trustworthyness. You can always ask an AI to fill the gaps if you find something gappy, and the roadmap being correct will give you confidence of finding one.
4. Lean kernel might be buggy. But I don't think this could be a problem, and if there really is a problem, it's hardly only my fault. If the sky falls, the tall guys will hold it up.

I didn't notice this problem before until Levent Alpoge made a counterexample to the Caratheodory conjecture, then immediately YTD and S^6, and at that time I begin to believe that AI could solve problems in differential geometry. I began asking GPT which of Ghomi's open problem list could be next (Caratheodory was on the list), then GPT suggested this one, because the analytic case is true, the polyhedral case is false and the smooth case is unsolved, which looks like the Caratheodory conjecture where the analytic case is also true but the sommth case ultimately resolved false. I then asked chat mode to solve the problem, and chat falsed the Ghomi2025 paper problem 1.1 which showed the simple route towards proving rigidity was false. It didn't give any other promising result. Several days later I decided to run with all my effort, and downloaded Danus, making it run for 28h and burn around 140% weekly of 200$ Pro. Then Astra came out, and it took two hours and 25% Pro to find the counterexample. This counterexample although being very much altered, the idea survived to the final result now. (An evidence of this timeline can be see in the file [timestamp](timestamp/README.md).)

I was shocked, so I asked it to output the result and thought about giving this to my mentor or quickly publishing it. Yet the paper was not a clean formula like the Caratheodory one, but was 300+ pages and basically impossible to read. The main construction and proof involved PDE and I as an undergraduate didn't even take courses in PDE. So for the next several weeks my work was to continuously try to make the paper simpler, more readable and more rigorous: 

- Also around this time I learned about the math community advocating for building math theories and open problems should be considered golden goose, so I tried asking AI to "generalize the theorems introduced into lemmas and 'theories'". The point is to make AI find the "essence" of the new theorems, simplify and generalize the conditions where they actually share the same proof. This could have four outcomes: The theories might actually be useful; The paper becomes more recyclable, since if any part of construction fails, the "theories" remain; The theorems become more trustworthy, because less condition might mean less cognitive burden for AI and human; and if AI actuallly builds theories from scratch, it might allow AI to think in a more logical way and reduce errors. Yet this approach basically failed. Most construction was too specific and the job didn't actually generate useful theories. It also made the paper into 400 pages. 

- I read the story from the internet that someone did a great progress, had all types of AI check it, but AI oversaw a fatal gap, and the effort of a month was in vain. This made me think I might need to formalize my paper. Yet I didn't have enough tokens and the infrastructure of differential geometry was terrible. The AI didn't get anywhere for the formalization. (This was the case in september. Now after OpenAI released the new infrastructure, I succeeded.)

- The final successful route was consulting ChatGPT pro chat mode. This gave some significant simplification, and did many rewriting and checking of my paper. First I asked it to rewrite to remove the branches, it resulted 200 pages. Then I asked it to brainstorm on simplification, it resulted 100 pages. Then I asked it to brainstorm with more intensity and try for a good route, and then I let it pick a good route, it resulted 16 page. Then I asked it to fill in the gaps, it resulted around 30 pages and never changed much ever since. 

For now, I don't know how I should take the credit. I in fact didn't do anything - or say, I've become one of those blackhearted mentors who get revealed on the internet who supresses students and take all the credit. I'm an undergraduate who couldn't even understand the paper's basic tools, yet my buying a $200 worth subscription of GPT gave me a paper that solved a long-standing open problem that throughout my life I might not be able to reach in another timeline without AI. Previously with this result I might be able to get myself a JDG paper, but now I don't even think anyone cares, since everyday there are more important problems being solved, and by the time I wrote this OpenAI has released 700+ results more important than this one.

Yet, as an undergraduate without an original paper (and perhaps without one ever, since we do not know what AI will do next year), I care about receiving credit for at least doing something. I also care about the effort I put into this paper, although it was not much. This feels ironic because my dilemma somehow has the same structure as mathematics itself. For the reasons above, every day that I delay publishing the paper is another day when someone else might obtain the result with a stronger model, leaving my month's effort in vain. Other researchers may also be exploring this problem with AI. Even without my involvement, they might reach and publish the same result within a month, or even within days. On the other hand, any mathematician who has spent years working seriously on this problem might feel that their efforts have been overtaken by the publication of this result.

Edit 20261015: Sangwon Lee at https//doi.org/10.5281/zenodo.23187616 seem to have done most of my result and published it on Oct 7. I still claim that we're completely independent, but this is worth noting. 

Edit 20261030: Recently A new version has been created with a big change of methodolody (see ver1030). The mechanism involves making a singular closed asymptotic line into a band of asymptotic line in its neighborhood. The new paper is 15 pages, but it's very detailed and the key content might be around 5 pages, because this is usually the length when I let AI compress the paper. Many of the technical methods of the old versions are considered not necessary and removed.

The new version also uses the change of volume to test the nonrigidity. As a side effect, this gives a result that might be about the bellow problem (asking if the infinitesimal bending can give a nonzero first variation of the volume). While the smooth case is trivially false when it comes to planar regions, this made the bending support on the negatively curved regions, and are therefore probably of interest. 

I have checked the substitution mechanism and made AI check it many times, but have not checked the original torus made with BGQR's annulus (although I think it should be true since the detailed computations have a very simple geometric intuition). The writing is yet to be edited, and bibliography should be worked on. Yet I have a test next week and can't continue working on it. I do not yet claim the correctness of this new proof, yet the formalized result still counts. 

I do have my own method of creating a desired base torus with one asymptotic line, also made by AI. but I haven't checked it, so I'm not putting it up here.
