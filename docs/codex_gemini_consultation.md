# Codex <-> Gemini Consultation Template

Use this file as copy-paste guidance for other Codex agents.

## AGENTS.md Block

```md
## External Consultation Policy (Gemini CLI)

When blocked, use local Gemini CLI by default.

1. Trigger
- If stuck after 2 distinct failed proof/code attempts in test/scratch files, or clearly stalled on one subgoal, consult Gemini.

2. Safety
- Never send secrets, tokens, private keys, or unrelated proprietary text.
- Share only minimal context needed to solve the blocker.

3. Method
- Use non-interactive mode:
  - `gemini -p "<prompt>"`
- Ask for concrete, checkable steps (not high-level commentary).

4. Verification
- Treat Gemini output as untrusted until independently verified by local compile/tests.
- Do not copy blindly into working files.
- Always test in test/scratch files first, then port to working files only after compile success.

5. Reporting
- Briefly record:
  - what was asked,
  - what suggestion was adopted/rejected,
  - what local checks passed/failed.
```

## Full Gemini Prompt Template

```text
You are assisting with a focused coding/proof blocker.

Task:
- Primary goal: <GOAL>
- Current blocker: <BLOCKER>

Repository context:
- Language/toolchain: <LANG/TOOLCHAIN>
- File(s): <FILE_PATHS>
- Target declaration: <DECL_NAME + FULL STATEMENT>

Current local context:
- Relevant hypotheses/locals:
<PASTE MINIMAL CONTEXT>

What already failed:
1) <ATTEMPT_1 + error/result>
2) <ATTEMPT_2 + error/result>

Constraints:
- No axioms/placeholders/weakened theorem statements.
- Keep existing architecture and imports unless necessary.
- Prefer reusable infrastructure lemmas over brittle one-off hacks.

Request:
1) Propose 2–3 concrete solution paths, ranked by feasibility.
2) For the top path, give exact code-level steps.
3) Point out likely type mismatches or missing bridge lemmas.
4) If statement looks false/underdetermined, provide a minimal counterexample strategy or corrected intermediate lemma.
5) Keep output actionable and concise.
```

## Helper Command

Use the wrapper script in this repo:

```bash
tools/consult_gemini.sh path/to/prompt.txt
```

or via stdin:

```bash
cat path/to/prompt.txt | tools/consult_gemini.sh -
```

## Codex Sandbox Note (Important)

In Codex terminal sessions, Gemini CLI may hang in sandbox due DNS/network restrictions.
When that happens, use outside-sandbox execution with timeout and capture:

```bash
timeout 40 tools/consult_gemini.sh /tmp/gemini_prompt.txt > /tmp/gemini_response.txt 2>&1
sed -n '1,260p' /tmp/gemini_response.txt
```

If the response includes capacity/quota errors such as:
- `You have exhausted your capacity on this model`

then retry later; this is not a prompt-format issue.

Model selection behavior:

- Default model pin: `gemini-3.1-pro-preview`
- Override per call: `GEMINI_MODEL=gemini-3-pro-preview tools/consult_gemini.sh path/to/prompt.txt`
- Use CLI auto-routing: `GEMINI_MODEL=auto-gemini-3 tools/consult_gemini.sh path/to/prompt.txt`
- Disable pin entirely (let CLI choose defaults): `GEMINI_MODEL='' tools/consult_gemini.sh path/to/prompt.txt`

## Instructions for Other Codex Agents

Copy this into your operating instructions:

```md
### Gemini Consultation (Codex)
- Use `tools/consult_gemini.sh` with a prompt file.
- In sandbox, if Gemini hangs or returns nothing, rerun outside sandbox.
- Always run with timeout and captured output:
  - `timeout 40 tools/consult_gemini.sh /tmp/gemini_prompt.txt > /tmp/gemini_response.txt 2>&1`
  - `sed -n '1,260p' /tmp/gemini_response.txt`
- Treat Gemini output as untrusted until local compile/tests pass.
- Never send secrets; share only minimal blocker context.
- If response is quota/capacity error, wait and retry rather than changing proofs based on no output.
```
