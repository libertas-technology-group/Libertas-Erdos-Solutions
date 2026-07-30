<h1 align="center">Libertas Superintelligence — Erdős Solutions</h1>

<p align="center">
  <img src="https://img.shields.io/badge/Libertas_Superintelligence-Proprietary-1a1a1a?style=flat-square" alt="Libertas Superintelligence — Proprietary">
  &nbsp;
  <img src="https://img.shields.io/badge/Lean-verified-5B21B6?style=flat-square" alt="Lean-verified">
  &nbsp;
  <img src="https://img.shields.io/badge/License-Apache_2.0-green?style=flat-square" alt="Apache 2.0">
  &nbsp;
  <img src="https://img.shields.io/badge/Lean-v4.27.0-blue?style=flat-square" alt="Lean v4.27.0">
</p>

Libertas Erdős Solutions contains mathematical solutions discovered autonomously by the **Libertas Superintelligence ©** platform - a proprietary system built using *open-weight* language models. Designed for solving the most complex problems in regulated industries, our technology uses transparent, "white-box" reasoning that allows human experts to review and audit domain-specific solutions. While most standard AI today acts like a "black box" - providing answers without showing how they were reached - our software platform reveals every logical problem-solving step, ensuring its reasoning is clear and verifiable.

Although our primary focus is enterprises working in high-stakes and highly regulated sectors, we stress-tested our system against open mathematical problems. Following the framework for AI-assisted mathematics outlined by Terence Tao [2][3], we have submitted these results to the Erdős Problems project [1] for independent verification. Just like with our enterprise solutions, we welcome expert mathematicians to critique our proofs, validate our results, and provide suggestions for improvement. The core result of our stress-testing showed a cost of **$5–$20** per **end-to-end** solution. This end-to-end solution includes knowledge discovery (finding a solution), Lean verification (proving it is mathematically correct), and LaTeX paper production (producing a final report for expert humans to review). This is a requirement for the regulated industries we serve. Technical details and scientific notes are provided below.

**Legal Notice:** Submitted to the Erdős Problems project [1] by Philip Ndikum and Serge Ndikum. (Please review the Licensing & Legal Notice section below for full authorship and legal information.) © 2026 Libertas Technology Group Limited. All rights reserved. This work was produced by Libertas Technology Group Limited using the Libertas Superintelligence © system - a proprietary AI system deployed using open-weight language models. This document is for informational and academic purposes only. The authors disclaim any representation or warranty, express or implied, regarding its accuracy, completeness, or suitability for any purpose. Nothing herein creates any liability or obligation on the part of Libertas Technology Group Limited.

## 📋 Table of Contents

- [Quick Start & Repository Architecture](#quick-start--repository-architecture)
- [What are Erdős Problems?](#what-are-erdős-problems)
- [Libertas Erdős Solutions](#libertas-erdős-solutions)
- [About Libertas Superintelligence & Technical Notes](#about-libertas-superintelligence--technical-notes)
- [Collaboration](#-collaboration)
- [Citing This Work](#-citing-this-work)
- [References](#-references)
- [Licensing & Legal Notice](#️-licensing--legal-notice)

## Quick Start & Repository Architecture

This repository provides machine-checked formal verification of mathematical solutions using Lean 4. To guarantee deterministic builds and reproducible verification across enterprise environments, the project relies on `lake` for dependency management and enforces strict version pinning for all toolchains and core libraries.

### Environment Specifications

| Component | Version |
|-----------|---------|
| Lean 4 Compiler | `leanprover/lean4:v4.27.0` |
| mathlib | `v4.27.0` |

**System prerequisites:** Environment provisioning requires `elan` (toolchain manager) and `lake` (build system). Refer to the official Lean 4 deployment documentation for system-specific installation procedures: https://lean-lang.org/lean4/doc/quickstart.html

### Build Execution

To verify the proofs locally, execute the standard Lake build sequence. The `--wfail` flag enforces a strict build standard by treating any compiler warning as a failure:

```bash
git clone https://github.com/libertas-technology-group/libertas-erdos-solutions
cd libertas-erdos-solutions
lake exe cache get
lake --wfail build
```

> **Expected Result:** A successful build yielding 0 sorries and 0 warnings, confirming that all target Lean modules compile deterministically with no unverified assertions (sorry). If you encounter any environment discrepancies or build issues, please open an issue or contact the maintainers directly.

### Architectural Layout

The repository implements a modular, problem-centric architecture. Verified proofs and supporting materials are isolated within dedicated `erdos/<problem-number>/` directories. This schema supports scalable integration of future problem sets, versioned verification snapshots, and independent modules. If formal peer review necessitates structural or logical modifications, changes will be tracked via version control and integrated into this directory schema. Supporting computational verification (e.g., Python oracles for any axioms not expressible in the current Lean kernel) is available in the relevant `erdos/<N>/python_verification/` subdirectory.


## What are Erdős Problems?

Paul Erdős (1913–1996), one of the most prolific mathematicians of the 20th century, proposed hundreds of conjectures across number theory, combinatorics, and analysis — many with cash prizes attached. The Erdős Problems project [1] maintains a public catalogue of approximately 353 open problems tracked against both human and AI contributions, while a community-maintained wiki [4] documents notable cases of AI-assisted solutions.

**Design of Experiments (DoE):** Informed by public commentary and frameworks from mathematicians such as Terence Tao and Thomas Bloom [1][2][3], we recognized that standard black-box AI often struggles with genuinely new, complex reasoning. Many open problems solved by AI to date were simply questions human mathematicians had not yet allocated time to complete or formalize. To properly evaluate Libertas Superintelligence ©, we deliberately designed all experiments to target harder and long-standing open problems. This allows us to rigorously stress-test our white-box system against true mathematical frontiers rather than low-hanging fruit. Just as with our enterprise workflows in regulated industries, we explicitly invite expert mathematicians to critique our proofs, validate our logic, and provide suggestions for improvement (see [Collaboration](#collaboration)).

## Libertas Erdős Solutions

This repository contains our formalized submissions of selected Erdős problems. Each solved problem is placed under an `erdos/<problem-number>/` directory; we will add or reorganize these subfolders as additional problems are solved or as reviewers provide consolidated feedback.

We welcome technical feedback from expert mathematicians. Please see the [Collaboration](#collaboration) section below or open an issue/PR following the contribution guidelines in CONTRIBUTING.md.

| Date | Problem | Part | History | Description (prior status) | Technical solution (summary) | Theorem | Status |
|------|---------|------|---------|----------------------------|------------------------------|---------|--------|
| July 2026 | **#12** | iii | Posed in 1970 by Erdős & Sárközy (Open for 56 years)[2, 3] | Part (iii) previously open; parts (i)/(ii) solved. | The proof constructs coprime and block sequences with controlled multiplicative gaps, establishes density bounds, and proves summability of reciprocals; independently verifiable via Lean 4. Key files: `Basic.lean`, `lemma_coprime_seq.lean`, `lemma_block_decomposition.lean`, `lemma_part_iii.lean`, `ErdosProblems/12.lean`. | `summable_of_isGood` | Lean-verified, pending professional mathematical review |

## About Libertas Superintelligence & Technical Notes

Libertas Superintelligence © is a proprietary autonomous AI system built
to solve the most complex problems faced by enterprises operating in highly-regulated sectors. Whilst our system is proprietary and closed-source, we have provided some technical and scientific notes for our Erdős solution stress-testing experiments:


| Category | Technical & Scientific Notes |
| :--- | :--- |
| Discovery as a Byproduct | Mathematical discovery was an unexpected result of stress-testing a system originally designed for problems faced by enterprises in highly-regulated sectors. |
| Open-Weight Models & Enterprise Deployment | The system utilizes open-weight language models driven by our proprietary mathematical and scientific software (Libertas Superintelligence). While our proprietary science and system design cannot be revealed, leveraging open-weight models means that our system can be completely self-hosted in a private environment, satisfying strict security and compliance requirements for regulated enterprise operations. |
| Mean Inference Cost Efficiency | In our stress tests, the mean inference cost varied from $5–$20 per problem, with variations driven by the execution demands of Lean verification. By employing a fundamentally different mathematical and scientific approach, this provides a substantial cost-efficiency improvement over published industry baselines, where state-of-the-art agents have resolved open Erdős problems at a per-problem cost of a few hundred dollars (before factoring in millions USD in compute and technical talent costs) [2, 3]. |
| White-Box Transparency & World Models | Operating as a fully white-box system, Libertas Superintelligence constructs explicit world models for the specific problem or domain being addressed. In pure mathematics, this allows the system to solve problems rapidly or provide a transparent evaluation of why a problem cannot be solved given current mathematical knowledge and our proprietary world models. |
| Autonomous Paper Production | The system autonomously produces LaTeX papers for each solved problem, which are available upon request alongside white-box explanations of the system's reasoning path. |
| Cost Variance & Autonomous Output | Cost varies by problem complexity and what the system generates. The system autonomously produces full LaTeX papers, world model documents explaining its reasoning, and Lean formalizations. Each output is independently verifiable. This is a requirement for the regulated industries we serve. Standard black-box AI cannot explain its reasoning. |

## 🤝 Collaboration

We kindly invite professional academics to review any solutions and provide feedback:

- Professional mathematical review and validation of these proofs.
- Suggestions for difficult Erdős problems our system can attempt.
- Opportunities to stress-test our system across finance, energy, biotechnology, and computational sciences.
- Co-authorship inquiries for any papers autonomously produced by our system.

Papers and technical reports are available upon request. Repository maintainers are reachable through their public professional profiles.

## 📝 Citing This Work

Code snippet

```bibtex
@misc{ndikum2026erdos,
  author       = {Philip Ndikum and Serge Ndikum},
  title        = {{L}ibertas {E}rd\H{o}s {S}olutions},
  year         = {2026},
  publisher    = {Libertas Technology Group Limited},
  note         = {Autonomously produced by the Libertas Superintelligence
                  system. Submitted to erdosproblems.com.},
  url          = {https://github.com/libertas-technology-group/libertas-erdos-solutions},
}
```

## 📚 References

1. Bloom, T. (2026). Erdős Problems. https://www.erdosproblems.com

2. Tao, T. (2026). "Mathematics in the Age of AI." SAIR Lecture, University of California, Berkeley, February 2026. https://www.youtube.com/watch?v=mS9Lr43cIB4

3. Tao, T. (2026). "Mathematical Methods and Human Thought in the Age of AI." Personal blog, March 29, 2026. https://terrytao.wordpress.com/2026/03/29/mathematical-methods-and-human-thought-in-the-age-of-ai

4. Sothanaphan, N., Tao, T. et al. (2026). AI Contributions to Erdős Problems. GitHub Wiki. https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erdos-problems

5. Sothanaphan, N., Tao, T. et al. (2026). Notable Cases of AI Contributions to Erdős Problems. GitHub Wiki. https://github.com/teorth/erdosproblems/wiki/Notable-cases-of-AI-contributions-to-Erdos-problems

6. DeepMind. (2026). Formal Conjectures. GitHub repository. https://github.com/google-deepmind/formal-conjectures

## ⚖️ Licensing & Legal Notice

Copyright © 2026 Libertas Technology Group Limited. All rights reserved.

All software is licensed under the Apache License, Version 2.0 (Apache 2.0); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the Apache 2.0 license at: https://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law or agreed to in writing, all software and materials distributed here under the Apache 2.0 license are distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the license for the specific language governing permissions and limitations under that license.

Proprietary Notice: This work was produced by Libertas Technology Group Limited using the Libertas Superintelligence © system, a proprietary AI system deployed using open-weight language models. This document and the associated code are for informational and academic purposes only. The authors disclaim any representation or warranty, express or implied, regarding its accuracy, completeness, or suitability for any purpose. Nothing herein creates any liability or obligation on the part of Libertas Technology Group Limited.