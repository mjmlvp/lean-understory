# ai-scratchpad — rules for AI working notes

The AI writes these notes to serve the user. The user does not read them.
They are fallible, written by an AI, and not endorsed by the user.

## Status of what is in here

- Nothing in a note counts as a decision or as a checked fact until verified.
- Before building on anything from a note, check it: against the code, the
  build, Mathlib's sources, measurements, or the user's recorded decisions.
- No place in the repository outranks another by where it sits. The user's
  decisions stand until the user changes them; factual claims are as good as
  their check. When two sources disagree, that is a signal. Check it, and if it
  needs a decision, raise it with the user. Never settle it silently.

## Keeping the notes useful

- Every note starts with a header:

  ```
  Date: YYYY-MM-DD (last revised)
  Status: draft | awaiting user decision | superseded (by …)
  Based on: what the note starts from
  Checked: what has been verified, and how; everything else is unchecked
  ```

- Notes must not contradict each other. Revise or mark the older one.
- Once the user approves something, record it in `docs/decisions.md` (or where
  it belongs) and note in the scratchpad where it went.
- Prune: remove what no longer serves the user, or mark it superseded.
- Notes only; nothing here is built or imported.
- Every note serves the user's goals. A note that drifts from them gets
  corrected or removed.
