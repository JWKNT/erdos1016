# Original technical writing

Use ASD-STE100-guided English for new or revised original explanations, proof prose, instructions, and interface text. Follow `../site-theme/docs/WRITING-STYLE.md` when that shared checkout is available.

- Keep one instruction in each sentence. Use the imperative. Put its condition first
- Use at most 20 words in an instruction sentence and 25 words in a descriptive sentence
- Keep each paragraph on one topic, with at most six sentences
- Use simple verbs, active voice, and consistent technical terms
- Preserve exact mathematical meaning, quantifiers, hypotheses, implications, proof status, and scientific limitations
- Preserve formulas, formal definitions, theorem statements, Lean declarations, citations, proper titles, and license or legal text
- Do not rewrite quoted sources, translations, reader source text, or material under `old/`
- Treat mathematical terminology and established UI actions as technical terms. Do not replace them with less precise ordinary words
- Describe this style as ASD-STE100-guided. Do not claim certified or exhaustive compliance without a complete dictionary review

For prose-only site edits, preserve markup, IDs, MathML, visual styles, and interaction logic. Run `node --test site/tests/*.mjs`. Compare protected mathematical content before and after the edit.

For manuscript edits, rebuild `paper/erdos1016.pdf` from `paper/erdos1016.tex`. Inspect the rendered pages. Copy the verified PDF to `site/paper.pdf` and check that both files are byte-identical.
