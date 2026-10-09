# Smooth tight nonrigidity

| Content | Location |
|---|---|
| Current illustrated manuscript, ver503 | [paper](paper/README.md) |
| Latest integrated Lean sources and exact proof status | [lean](lean/README.md) |
| Interactive numerical geometry and illustrated construction | [visualization](visualization/README.md) |

The Lean formalization remains **incomplete**. The latest integrated audit records 1,403 modules and 17,564 declarations; the final existence theorem is pending. The numerical meshes illustrate the construction and do not certify it.

To explore the visualization, serve this repository root:

```sh
python -m http.server 8000 --bind 127.0.0.1
```

Then open **http://127.0.0.1:8000/visualization/index.html**. Detailed build and usage instructions are in each directory's README.

## AI usage and my personal words

This paper is written "assisted" by (in fact JUST BY) ChatGPT-5.6-Sol, ChatGPT-6-Astra and ChatGPT-6.1-Sol. 

I do not claim the correctness of this paper yet. This has passed the check of AI in various different versions, and none found any fatal errors, and this is all I can now give (20261009). I'm still working on the human checking and formalization. About the credit, you can read my story and decide for yourself.

I didn't notice this problem before until Levent Alpoge made a counterexample to the Caratheodory conjecture, then immediately YTD and S^6, and at that time I begin to believe that AI could solve problems in differential geometry. I began asking GPT which of Ghomi's open problem list could be next (Caratheodory was on the list), then GPT suggested this one, because the analytic case is true, the polyhedral case is false and the smooth case is unsolved, which looks like the Caratheodory conjecture where the analytic case is also true but the sommth case ultimately resolved false. I then asked chat mode to solve the problem, and chat falsed the Ghomi2025 paper problem 1.1 which showed the simple route towards proving rigidity was false. It didn't give any other promising result. Several days later I decided to run with all my effort, and downloaded Danus, making it run for 28h and burn around 140% weekly of 200$ Pro. Then Astra came out, and it took two hours and 25% Pro to find the counterexample. This counterexample although being very much altered, the idea survived to the final result now. (An evidence of this timeline can be see in the file [timestamp](timestamp/README.md).)

I was shocked, so I asked it to output the result and thought about giving this to my mentor or quickly publishing it. Yet the paper was not a clean formula like the Caratheodory one, but was 300+ pages and basically impossible to read. The main construction and proof involved PDE and I as an undergraduate didn't even take courses in PDE. So for the next several weeks my work was to continuously try to make the paper simpler, more readable and more rigorous: 

- Also around this time I learned about the math community advocating for building math theories and open problems should be considered golden goose, so I tried asking AI to "generalize the theorems introduced into lemmas and 'theories'". The point is to make AI find the "essence" of the new theorems, simplify and generalize the conditions where they actually share the same proof. This could have four outcomes: The theories might actually be useful; The paper becomes more recyclable, since if any part of construction fails, the "theories" remain; The theorems become more trustworthy, because less condition might mean less cognitive burden for AI and human; and if AI actuallly builds theories from scratch, it might allow AI to think in a more logical way and reduce errors. Yet this approach basically failed. Most construction was too specific and the job didn't actually generate useful theories. It also made the paper into 400 pages. 

- I read the story from the internet that someone did a great progress, had all types of AI check it, but AI oversaw a fatal gap, and the effort of a month was in vain. This made me think I might need to formalize my paper. Yet I didn't have enough tokens and the infrastructure of differential geometry was terrible. The AI didn't get anywhere for the formalization. 

- The final successful route was consulting ChatGPT pro chat mode. This gave some significant simplification, and did many rewriting and checking of my paper. First I asked it to rewrite to remove the branches, it resulted 200 pages. Then I asked it to brainstorm on simplification, it resulted 100 pages. Then I asked it to brainstorm with more intensity and try for a good route, and then I let it pick a good route, it resulted 16 page. Then I asked it to fill in the gaps, it resulted around 30 pages and never changed much ever since. 

For now, I don't know how I should take the credit. I in fact didn't do anything - or say, I've become one of those blackhearted mentors who get revealed on the internet who supresses students and take all the credit. I'm an undergraduate who couldn't even understand the paper's basic tools, yet my buying a $200 worth subscription of GPT gave me a paper that solved a long-standing open problem that throughout my life I might not be able to reach in another timeline without AI. Previously with this result I might be able to get myself a JDG paper, but now I don't even think anyone cares, since everyday there are more important problems being solved, and by the time I wrote this OpenAI has released 700+ results more important than this one.

Yet me as an undergrad who didn't have (or maybe won't ever have, since we don't know what AI would do next year) an actual original paper, I care about the credit of at least doing something, and I do care about the effort I put into this paper - although not much. Somehow this becomes very ironic because somehow my dilemma shares the same structure as math itself. Because of above reasons, one day I don't publish the paper one day another person might take it with a stronger model, my one-month effort in vain (I fact, Ding's paper on Oct 6 might be a sign that he's been attacking this problem with AI as well. Without me, he having the very same AI could publish this result within a month or even within days). Yet as a mathematician like Ghomi, a year (since 2025) of effort on this problem might still be in vain on the publishing of my paper. 
