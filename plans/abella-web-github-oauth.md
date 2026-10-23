# Plan: GitHub OAuth for Abella Web

**Status:** in progress; Phases 0-2 complete (2026-10-23).

**Scope:** a sidequest to `plans/abella-web/v10.md`. It changes only how a
GitHub token is obtained. The GitHub workspace, Octokit client, read path,
and atomic commit path stay as they are.

**Proposes replacing:** v10's "PAT only; no redirect OAuth flow" decision
for GitHub. The earlier decision was correct for a purely static site
without any server-side component. This plan accepts a small Cloudflare
Worker as the one piece of server-side infrastructure, so the decision is
revisited deliberately rather than accidentally. v10 remains the source of
truth until the implementation is recorded in v11.

**Estimate:** 3.5 to 4.5 engineer-days for Phases 0 through 4, plus a
separate Phase 5 deployment window for Cloudflare, DNS, and the
production OAuth app.

## 1. Summary

Abella Web currently asks the user to create a fine-grained personal
access token (PAT) and paste it into the GitHub dialog. That works, but it
is the main onboarding friction in the GitHub workflow: the user has to
navigate GitHub settings, choose the right permissions and repositories,
copy the token, and paste it back.

This plan adds a "Sign in with GitHub" flow:

1. The frontend generates a random `state` and a PKCE verifier/challenge.
2. It opens GitHub's authorization page in a popup.
3. GitHub redirects the popup to a static callback page on
   `abella-prover.org`.
4. The callback page sends the short-lived `code` and `state` back to the
   opener with `postMessage`. It never exchanges the code and never sees
   the token.
5. The main tab verifies `state`, then asks a Cloudflare Worker to exchange
   the code for an access token. The Worker is the only component that
   knows the OAuth client secret.
6. The main tab validates the token with `GET /user`, stores it in
   `sessionStorage` exactly like a PAT, and hands it to the existing
   Octokit client.

The PAT path remains available as an advanced fallback. Public
repositories still load without any token.

## 2. Review of the sketch

The sketch is directionally correct. A static page cannot hold an OAuth
client secret, so a minimal token-exchange proxy is the right shape. The
following parts need to be made explicit before implementation.

- **Register an OAuth app with homepage and callback.** Correct. Use an
  exact callback URL, a separate app for local development, and disable
  wildcard callback matching.
- **Redirect to `github.com/login/oauth/authorize` with `scope=repo` and
  `state`.** Correct, but incomplete. Add PKCE, default to `public_repo`,
  make `repo` an explicit opt-in, and use a popup rather than a full-page
  redirect.
- **GitHub redirects to `?code=...&state=...`.** Correct. Use a dedicated
  static callback page. Do not put a token in a URL and do not exchange in
  the popup.
- **Worker exchanges the code and returns a token with CORS headers.**
  Correct. Restrict CORS to the exact site origin, validate the redirect
  URI, never log the code or token, add rate limiting, and return only the
  access token and granted scope.
- **"Initialize it in octokit."** Correct. Validate the token with
  `/user`, store it in `sessionStorage`, handle 401 by clearing it, and
  keep the existing `GitHubWorkspace.authorize` path.

### 2.1 The important corrections

1. **A full-page redirect loses state.** A GitHub workspace is not
   automatically reconnected after a page reload; the saved descriptor is
   restored as a read-only memory workspace. If the user is in the middle
   of a commit and the page navigates to GitHub, dirty edits and the
   pending commit intent are lost. A popup keeps the app, the prover, and
   the pending commit alive.
2. **`state` alone is not enough.** GitHub now supports PKCE. Add an
   S256 challenge so an intercepted authorization code cannot be
   exchanged without the verifier that lives only in the main tab.
3. **`scope=repo` is broader than the current fine-grained PAT.** OAuth
   App scopes are account-wide; they cannot be limited to selected
   repositories. The plan defaults to `public_repo` and makes `repo` an
   explicit, clearly labelled option. The PAT path remains for users who
   need per-repository least privilege.
4. **CORS must not be `*`.** The Worker handles codes that are bound to
   the Abella Web OAuth app. An exact origin allowlist, a fixed redirect
   URI, PKCE, and rate limiting are all part of the design.
5. **The callback URL must be a real file.** The deployed site is a static
   tree under `/web/`. A dedicated `web/github-callback.html` avoids
   booting the prover and CodeMirror just to finish a login.
6. **The sketch does not say where the token goes.** It must never enter
   `localStorage`, a URL, a log, or an error message. It stays in
   `sessionStorage`, like the existing PAT.

### 2.2 Verdict

The sketch makes sense as a feature request and as an architecture sketch.
It should not be implemented literally. Implement the same flow with PKCE,
a popup, a dedicated callback page, a strict Worker contract, and the PAT
fallback. That is the design in the rest of this document.

## 3. Goals and non-goals

### 3.1 Goals

- Let a user connect GitHub with a GitHub-hosted authorization page instead
  of creating and pasting a PAT.
- Keep the OAuth client secret off the static site.
- Keep existing GitHub reads, writes, commits, conflict handling, and
  read-only public access unchanged.
- Preserve the current project, prover state, and pending commit across
  the GitHub round trip.
- Provide a safe, testable Worker with a narrow, documented contract.
- Keep a PAT fallback for least-privilege users and for cases where the
  Worker is unavailable.
- Make the failure modes (cancelled login, blocked popup, bad state,
  revoked token, insufficient scope) actionable and non-destructive.

### 3.2 Non-goals

- Replacing the `GitHubWorkspace` abstraction or the Octokit client.
- Supporting GitLab, Codeberg/Gitea, Dropbox, or any other provider.
- A GitHub App or device-flow implementation. Both are discussed as
  future alternatives in section 12.
- Refresh tokens or automatic token rotation. v1 uses a normal OAuth App
  access token and relies on `sessionStorage` plus revocation.
- Server-side sessions, cookies, or storing tokens in the Worker.
- A full-page OAuth redirect fallback. If the popup cannot be used, the
  user can use a PAT or allow popups.
- Changing the commit protocol, branch conflict handling, or workspace
  file policy.
- Adding a general-purpose OAuth library to the frontend. Web Crypto and
  `fetch` are enough for this flow.

## 4. Architecture

### 4.1 Flow

```text
main tab: https://abella-prover.org/web/
  |
  |  1. user clicks "Sign in with GitHub"
  |  2. generate state + PKCE verifier/challenge
  |  3. window.open(authorize URL)
  v
popup: https://github.com/login/oauth/authorize
  |
  |  4. user approves the requested scope
  v
popup: https://abella-prover.org/web/github-callback.html
       ?code=...&state=...
  |
  |  5. postMessage({code, state}) to window.opener
  |  6. close the popup
  v
main tab
  |
  |  7. verify event.origin, event.source, and state
  |  8. POST {code, codeVerifier} to the Worker
  v
Cloudflare Worker: https://oauth.abella-prover.org
  |
  |  9. POST https://github.com/login/oauth/access_token
  |     client_id + client_secret + code + redirect_uri
  |     + code_verifier
  v
GitHub
  |
  | 10. access token + granted scope
  v
Worker -> main tab
  |
  | 11. validate GET https://api.github.com/user
  | 12. save token in sessionStorage
  | 13. hand token to Octokit / GitHubWorkspace
  v
existing GitHub read and commit code
```

### 4.2 Why a proxy is still needed

GitHub's web application flow requires both the client ID and the client
secret at the token endpoint. PKCE protects the code, but it does not
remove the client-secret requirement. The static page cannot keep a
secret, so one of these is necessary:

- a small token-exchange endpoint (this plan);
- the device flow, which needs no secret but requires the user to copy a
  code into GitHub (worse UX);
- a GitHub App, which has a different setup and permission model.

The Worker is deliberately minimal: two routes, no storage, no sessions,
and no token persistence. It is an exchange endpoint, not a backend.

### 4.3 Why a popup rather than a redirect

Here "popup" means a separate browser window (an auxiliary browsing
context) opened with `window.open`, not an HTML `<dialog>` inside Abella
Web. The existing GitHub dialog remains a modal `<dialog>` for choosing
the scope and entering a PAT; it launches the popup. The GitHub
authorization page must be a top-level navigation because GitHub refuses
to be framed, so it cannot be embedded in a modal or iframe.

Some browsers may present the popup as a tab rather than a floating
window. The flow only depends on `window.opener` and `postMessage`, so
either presentation works.

A full-page redirect would unload the main document. That would lose:

- the in-memory prover session;
- the current CodeMirror state;
- unsaved GitHub workspace edits;
- `pendingCommitMessage` and the dialog mode.

The current persistence model does not reconnect a GitHub workspace
automatically. A popup avoids all of this. The callback page is a small,
static relay that never runs the prover.

A popup can be blocked. The UI must detect that, show a clear message, and
leave the PAT field available. It should not silently fail.

Open the popup synchronously from the click handler. Do not add
`noopener` to the `window.open` call: the callback page needs
`window.opener` to return the code. The callback sends no token, so losing
the opener would only make the flow fail closed.

### 4.4 Trust boundaries

- **Main tab:** trusted application code. Holds the PKCE verifier and the
  access token for the tab's lifetime.
- **GitHub authorization page:** trusted identity provider. It sees the
  requested scope and the user's decision, not the client secret.
- **Callback page:** same-origin static page. It handles a short-lived
  code and forwards it to the opener. It must not exchange the code or
  store a token.
- **Cloudflare Worker:** trusted exchange component. Holds the client
  secret. It sees the code and the PKCE verifier in transit, but never
  receives the user's password and never persists either value.
- **GitHub token endpoint:** the only place where the client secret is
  presented.

## 5. Design

### 5.1 OAuth app registration

Create two GitHub OAuth Apps: one for production and one for local
development. Do not use the production secret on a developer machine.

Production app (create in Phase 5, not during local development):

- Application name: `Abella Web`
- Homepage URL: `https://abella-prover.org/web/`
- Authorization callback URL:
  `https://abella-prover.org/web/github-callback.html`
- Wildcard callback matching: disabled

Development app (create in Phase 0):

- Application name: `Abella Web (dev)`
- Homepage URL: `http://127.0.0.1:8000/`
- Authorization callback URL:
  `http://127.0.0.1:8000/github-callback.html`
- Wildcard callback matching: disabled

Notes:

- The callback URL must match exactly. Do not rely on wildcard matching.
- The client ID is public and can appear in the Worker configuration and
  in the frontend configuration response.
- The client secret is stored only as a Cloudflare Worker secret.
- Verify that "Expire access tokens" is disabled for the app. Do not
  enable it for v1. If that feature is enabled later, the Worker must
  return the refresh token and the frontend must implement refresh. That
  is a separate plan.
- Record the production client ID in the Worker configuration and the
  UI's "review or revoke access" link:
  `https://github.com/settings/connections/applications/<client_id>`.

### 5.2 Scopes and least privilege

The connect dialog offers two modes:

- **Public repositories only (default):** request `public_repo`.
  Read/write public repositories.
- **Allow private repositories (opt-in):** request `repo`. Read/write
  private repositories as well.

`repo` is broader than `public_repo` and cannot be restricted to selected
repositories. The checkbox label and help text must say so. Users who need
per-repository access should use a fine-grained PAT instead.

If the user has a public-only token and tries to load a private
repository, the existing 404 path should offer a targeted action:
"Reconnect with private repository access." That starts a new OAuth flow
with `repo` and replaces the token in `sessionStorage`.

GitHub may return fewer scopes than requested. The token exchange response
contains the granted `scope`. The UI should warn if the returned scope
does not include the requested repository access, but it should not
discard an otherwise usable token.

### 5.3 Frontend OAuth client

Add `support/ts/web/github-oauth.ts` and a small dependency-free
`support/ts/web/oauth-callback.ts`. Keep both side-effect free and free of
Octokit imports so the callback bundle stays tiny and the modules are easy
to unit test.

`oauth-callback.ts` owns `OAuthCallback` and `parseOAuthCallback(search)`.
It has no imports. The main OAuth client and the callback page both use
it, so the callback bundle does not pull in workspace or Octokit code.

Public surface:

```ts
export interface GitHubOAuthConfig {
  clientId: string;
  redirectUri: string;
}

export async function fetchGitHubOAuthConfig(
  workerUrl: string
): Promise<GitHubOAuthConfig>;

export async function createOAuthRequest(
  config: GitHubOAuthConfig,
  scope: "public_repo" | "repo"
): Promise<{ state: string; verifier: string; url: string }>;

// parseOAuthCallback and OAuthCallback live in oauth-callback.ts.

export async function exchangeGitHubCode(
  workerUrl: string,
  code: string,
  verifier: string
): Promise<{ token: string; scope: string }>;

export async function validateGitHubToken(
  token: string
): Promise<{ login: string }>;
```

Implementation requirements:

- Generate `state` and the verifier with
  `crypto.getRandomValues(new Uint8Array(32))`, encoded as base64url.
- The verifier is 43 characters and uses only
  `[A-Za-z0-9-._~]` (base64url without padding is acceptable).
- The challenge is `base64url(SHA-256(UTF-8(verifier)))`, using
  `crypto.subtle.digest("SHA-256", ...)`.
- Build the authorize URL with:
  - `client_id`
  - `redirect_uri`
  - `scope`
  - `state`
  - `code_challenge`
  - `code_challenge_method=S256`
- Do not include a client secret anywhere in the frontend.
- `fetchGitHubOAuthConfig` calls `GET <workerUrl>/github/config` with
  `credentials: "omit"` and `cache: "no-store"`.
- `exchangeGitHubCode` calls `POST <workerUrl>/github/token` with JSON
  `{code, codeVerifier}`. It must not send `redirect_uri`; the Worker
  derives it from the request origin.
- `validateGitHubToken` calls `GET https://api.github.com/user` with
  `Authorization: Bearer <token>`, `Accept: application/vnd.github+json`,
  and `X-GitHub-Api-Version: 2022-11-28`.
- Map failures to `WorkspaceError` so the existing
  `workspaceMessage(error)` path can display them:
  - cancelled/denied -> `cancelled`
  - bad token -> `permission-denied`
  - network/Worker/GitHub failure -> `unavailable`
  - protocol/configuration error -> `io`

The pending flow lives in a module variable in `main.ts`, not in
`sessionStorage`:

```ts
interface PendingOAuth {
  state: string;
  verifier: string;
  popup: Window;
  intent: "connect" | "commit";
  repoInput?: string;
  commitMessage?: string;
  requestedScope: "public_repo" | "repo";
  createdAt: number;
  messageReceived: boolean;
}
```

Keeping the verifier in memory means a page reload safely aborts the
flow. The popup's message is ignored because there is no matching pending
state. The user simply tries again.

Clear the pending flow on success, on any error, after 10 minutes (the
GitHub code lifetime), and when the popup closes without sending a
message. A low-frequency `popup.closed` check should wait a short grace
period before giving up so a queued `postMessage` can still arrive.
Starting a second flow closes the previous popup and replaces the pending
flow.

### 5.4 Callback page

Add two tracked files:

- `web/github-callback.html`
- `support/ts/web/github-callback.ts`

The build produces `web/github_callback.js`.

`web/github-callback.html` is deliberately minimal:

- no prover, no CodeMirror, no Octokit;
- one same-origin script tag (`github_callback.js`);
- `<meta name="referrer" content="no-referrer">`;
- a short "Finishing GitHub sign-in..." message and a manual link back to
  `./` if the popup cannot close itself.

The callback script:

1. Reads `code`, `state`, `error`, and `error_description` from
   `location.search`.
2. If `window.opener` exists and is not the current window, posts:
   ```ts
   {
     type: "abella-github-oauth",
     code,
     state,
     error,
     errorDescription
   }
   ```
   with `window.location.origin` as the target origin.
3. Calls `history.replaceState(null, "", location.pathname)` so the code
   is removed from the visible URL.
4. Closes the popup after the message is posted. If `window.close()` is
   refused, the page shows "You can close this window."
5. If there is no opener, does not exchange the code. It shows an error
   telling the user to start from Abella Web.

The callback page must never:

- call the Worker;
- store a token;
- call Octokit;
- include a client secret;
- put a token or code in a redirect URL.

### 5.5 Cloudflare Worker

Create a small, standalone package:

```text
support/oauth-worker/
  package.json
  package-lock.json
  tsconfig.json
  wrangler.jsonc
  .dev.vars.example
  README.md
  src/index.ts
  src/index.test.ts
```

The Worker is a separate npm package. `make web` does not install or
build it, so the static-site build keeps working without a Cloudflare
toolchain.

The Worker has two routes.

#### `GET /github/config`

Returns the public configuration needed to start a flow.

Request:

```http
GET /github/config
Origin: https://abella-prover.org
```

Response:

```json
{
  "clientId": "Iv1.0123456789abcdef",
  "redirectUri": "https://abella-prover.org/web/github-callback.html"
}
```

- Allowed only for the exact `ALLOWED_ORIGIN`.
- `Cache-Control: no-store`.
- If the Worker is not configured, return 503. The frontend then hides the
  OAuth button and leaves the PAT path available.
- It returns no secret and no token.

#### `POST /github/token`

Request:

```http
POST /github/token
Origin: https://abella-prover.org
Content-Type: application/json

{"code":"...","codeVerifier":"..."}
```

Response on success:

```json
{"token":"gho_...","scope":"public_repo"}
```

Response on failure:

```json
{"error":"invalid_code","message":"GitHub rejected the code."}
```

Status mapping:

- 400: invalid request, malformed body, or a code/verifier that GitHub
  rejects;
- 403: missing or mismatched `Origin`;
- 405: method not allowed;
- 413: body larger than 4 KiB;
- 502: GitHub or network failure;
- 503: Worker misconfigured;
- 504: upstream timeout.

All error bodies use the `{error, message}` shape above.

- Allowed only for the exact `ALLOWED_ORIGIN`.
- Reject missing or mismatched `Origin` with 403.
- Reject methods other than `POST` (and `OPTIONS` for preflight).
- Reject bodies larger than 4 KiB, malformed JSON, or missing/oversized
  `code`/`codeVerifier`.
- Use the Worker's configured `REDIRECT_URI`; do not accept a
  client-supplied redirect URI.
- Exchange the code with:
  ```http
  POST https://github.com/login/oauth/access_token
  Accept: application/json
  Content-Type: application/x-www-form-urlencoded

  client_id=...&client_secret=...&code=...&redirect_uri=...&code_verifier=...
  ```
- Use a 10-second timeout (`AbortSignal.timeout(10_000)`) and
  `redirect: "manual"`; reject any 3xx response. Workerd rejects
  `redirect: "error"`, and manual redirects preserve the no-follow rule.
- Handle GitHub's HTTP 200 JSON error responses (for example
  `bad_verification_code`, `access_denied`), not only non-2xx statuses.
- Return only `token` and `scope`. Drop `refresh_token`, `token_type`, and
  any other fields.
- Never log the code, verifier, client secret, or token.
- `Cache-Control: no-store`, `X-Content-Type-Options: nosniff`.

Worker environment:

- `GITHUB_CLIENT_ID` (plain var): public OAuth app client ID.
- `GITHUB_CLIENT_SECRET` (secret): OAuth app client secret.
- `ALLOWED_ORIGIN` (plain var): exact site origin, for example
  `https://abella-prover.org`.
- `REDIRECT_URI` (plain var): exact callback URL registered with GitHub.

Use one Worker deployment per environment. Production allows only
`https://abella-prover.org`. Local development uses `wrangler dev` with
`http://127.0.0.1:8000` and the dev OAuth app. Do not add a
user-controlled Worker URL override to the production page.

The site must be served from that canonical origin. Redirect
`www.abella-prover.org` to the apex (or deploy a second Worker
configuration for the `www` origin), otherwise the OAuth button will fail
from the alternate host.

CORS:

- `Access-Control-Allow-Origin: <ALLOWED_ORIGIN>` only.
- `Vary: Origin`.
- `Access-Control-Allow-Methods: POST, GET, OPTIONS`.
- `Access-Control-Allow-Headers: Content-Type`.
- `Access-Control-Max-Age: 600`.
- Do not set `Access-Control-Allow-Credentials`; the flow uses no cookies.
- Apply the CORS headers to success and error responses for the allowed
  origin, so the frontend can read an actionable error instead of seeing
  an opaque network failure.

Rate limiting:

- Configure a Cloudflare rate-limit rule for `POST /github/token`, for
  example 30 requests per minute per IP, action block for 60 seconds.
- The Worker itself does not need a distributed counter. PKCE already
  makes stolen codes hard to use; rate limiting is for abuse and cost
  control.
- Document the rule in `support/oauth-worker/README.md`.

### 5.6 Token lifecycle and storage

- Reuse the existing session storage key and helpers in
  `support/ts/web/github-auth.ts`:
  - `saveGitHubToken`
  - `loadGitHubToken`
  - `clearGitHubToken`
- The token is session-scoped: it survives a reload in the same tab and is
  cleared when the tab closes or the user disconnects. A fresh tab does
  not share it. A duplicated or opener-created tab may inherit a copy,
  which is standard `sessionStorage` behavior.
- Never write the token to `localStorage`, a URL, the DOM, a log, or an
  error message.
- After exchange, call `GET /user`. If it fails with 401, clear the token
  and show a reconnect message.
- If any later GitHub request returns 401, clear the stored token and
  prompt for reconnection. Implement this by exposing the HTTP status on
  `WorkspaceError` (for example an optional `status?: number`) or by
  adding a dedicated auth error flag; do not treat 403 as an expired
  token.
- Keep the existing `Disconnect` action. It clears the token and calls
  `GitHubWorkspace.clearToken()`.
- Add a "Review or revoke access" link to the dialog. It is a GitHub
  settings page, not a token operation in the app.

### 5.7 UI integration

The existing GitHub dialog in `web/index.html` and
`support/ts/web/main.ts` gains:

- a primary `Sign in with GitHub` button;
- a `Allow private repositories (repo scope)` checkbox;
- a collapsed `Use a personal access token instead` section containing
  the existing token field and Load/Authorize button;
- a short note explaining that GitHub OAuth apps grant account-wide
  scopes and that a fine-grained PAT is available for least privilege;
- a status/error area that is used by both OAuth and PAT paths;
- a "Review or revoke access" link when a client ID is known.

Dialog states:

- **Checking Worker config:** OAuth button disabled, short status.
- **OAuth available:** OAuth button enabled; PAT section collapsed.
- **OAuth unavailable:** OAuth button hidden; PAT section expanded with an
  explanation.
- **Starting popup:** OAuth button disabled; status "Waiting for GitHub...".
- **Popup blocked:** error with "Allow popups for this site, or use a token
  below."
- **Cancelled at GitHub:** error "GitHub sign-in was cancelled." Pending
  flow cleared.
- **State mismatch:** error "Sign-in state did not match. Try again." No
  exchange.
- **Success:** dialog closes or resumes the pending action; status shows
  the account login.
- **Worker/GitHub error:** error in the dialog; PAT fallback remains.

The dialog must fetch the Worker config lazily, the first time it opens,
not at page startup. A failed config request must not prevent the dialog
from opening.

### 5.8 Workspace integration

No changes to the Octokit read or commit code are expected.

Refactor the existing GitHub submit handler in `main.ts` into a shared
completion path:

```ts
async function applyGitHubToken(
  token: string,
  scope: string,
  intent: "connect" | "commit"
): Promise<void>
```

Both the PAT form and the OAuth success handler call it.

Connect intent:

1. Before starting OAuth, validate the repository input and run the
   existing dirty-project confirmation. Do not send the user to GitHub
   only to make them cancel after returning.
2. Save the token and validate it with `/user`.
3. Close the dialog.
4. Call the existing `loadGitHubRepository(input, token)` path with the
   repository input stored in the pending flow.
5. If the repository is private and the token lacks `repo`, show the
   targeted "Reconnect with private repository access" action.

Commit intent:

1. Check that the current workspace is a `GitHubWorkspace`.
2. Call `workspace.authorize(token)`.
3. Save the token only after authorization succeeds.
4. Close the dialog.
5. Resume `performCommit(pendingCommitMessage)`.

`GitHubWorkspace.authorize` keeps its current checks (`/user` plus
`repos.get` and `canPush`). The token is an ordinary OAuth token and
Octokit accepts it as `auth`, exactly like a PAT.

Update auth-related copy that currently assumes a fine-grained PAT:

- "Use a token with Contents: Read and write" becomes "Use a token with
  write access, or reconnect with an account that can push."
- Private-repository 404 text offers the private-scope reconnect.
- The PAT help text remains specific about `Contents: Read` and
  `Contents: Read and write`.

### 5.9 Configuration and deployment

Worker URL:

- Recommended production URL: `https://oauth.abella-prover.org`.
- Fallback if DNS cannot be delegated: the Worker's `workers.dev` URL.
  The exact URL must be used in the CSP and the frontend build.
- Keep the Worker off the `/web/` static tree. `make publish-web` must not
  be able to overwrite it.

Frontend configuration:

- Add `support/ts/web/github-oauth-config.ts` with a production default
  and a build-time override:
  ```ts
  declare const __GITHUB_OAUTH_WORKER__: string | undefined;

  export const GITHUB_OAUTH_WORKER =
    typeof __GITHUB_OAUTH_WORKER__ === "string"
      ? __GITHUB_OAUTH_WORKER__
      : "https://oauth.abella-prover.org";
  ```
- Add `web:js:dev` and `web:build:dev` scripts alongside the production
  scripts. `web:js:dev` defines `__GITHUB_OAUTH_WORKER__` as
  `http://127.0.0.1:8787`; `web:build:dev` uses it and also builds the
  callback, worker, and CSS.
- Do not expose a query-parameter or `localStorage` override in
  production. A malicious Worker URL would receive authorization codes.
- The Worker's `/github/config` response is the source of truth for
  `clientId` and `redirectUri`. The frontend does not hardcode either.

CSP:

- Add the Worker origin to `connect-src`:
  ```text
  connect-src 'self' https://api.github.com
    https://raw.githubusercontent.com https://oauth.abella-prover.org;
  ```
- The existing GitHub backend uses both `api.github.com` and
  `raw.githubusercontent.com`; verify the deployed CSP covers both while
  adding the Worker.
- The callback page needs no new `script-src` permission because it loads
  a same-origin script.
- Do not set `Cross-Origin-Opener-Policy: same-origin` on `/web/` if the
  popup flow is to work. `same-origin-allow-popups` is acceptable; verify
  the actual deployment headers. If the site requires the stricter
  policy, the popup flow must be replaced by a redirect flow, which is out
  of scope for this plan.

Static files and build:

- Track `web/github-callback.html` (the global `*.html` ignore rule needs
  a `!web/github-callback.html` exception).
- Generate `web/github_callback.js` and ignore it.
- Add `web:callback` to `support/package.json` and to `web:build`:
  ```json
  "web:callback": "esbuild ./ts/web/github-callback.ts --bundle --format=iife --minify --outfile=../web/github_callback.js"
  ```
- Add the callback bundle to `support/scripts/check-web-size.mjs` with a
  small gzip budget (for example 4 KiB).
- Serve `web/github-callback.html` with `Cache-Control: no-store`,
  `Referrer-Policy: no-referrer`, `X-Frame-Options: DENY`, and
  `frame-ancestors 'none'` where the deployment configuration allows
  per-file headers.
- `make publish-web` already copies the whole `web/` tree, including the
  new callback files.

Worker build and CI:

- Add `support/oauth-worker/package.json` with `check`, `test`, `dev`, and
  `deploy` scripts.
- Use `tsc --noEmit` with `@cloudflare/workers-types` and a Node-only test
  bundle.
- Add a CI job that runs `npm ci`, `npm run check`, and `npm test` in
  `support/oauth-worker`. CI must not use real OAuth secrets.
- Add optional Makefile targets:
  ```make
  oauth-worker-check:
      ( cd support/oauth-worker && npm ci && npm run check && npm test )

  oauth-worker-deploy:
      ( cd support/oauth-worker && npm ci && npm run deploy )
  ```
- Do not add the Worker deployment to `publish-web`; it is an independent
  operation with its own environment and secret.

Git ignore additions:

```text
/web/github_callback.js
/support/oauth-worker/node_modules/
/support/oauth-worker/.wrangler/
/support/oauth-worker/.test/
/support/oauth-worker/.dev.vars
```

### 5.10 Local development

OAuth development does not require `abella-prover.org`. GitHub permits
loopback HTTP callbacks, and neither the production Worker nor the
production DNS is used. All of that is deferred to Phase 5. Use a fixed
loopback origin throughout:

- main page: `http://127.0.0.1:8000/`
- callback: `http://127.0.0.1:8000/github-callback.html`
- Worker: `http://127.0.0.1:8787`

Use `127.0.0.1`, not `localhost`. They are different origins, and GitHub
recommends the loopback literal. The dev OAuth app callback, the Worker
`ALLOWED_ORIGIN`, and the Worker `REDIRECT_URI` must all agree.

Serve the generated `web/` tree as the document root:

```sh
cd web
python3 -m http.server 8000 --bind 127.0.0.1
```

Then open `http://127.0.0.1:8000/`.

`python3 -m http.server` is enough for OAuth testing. It does not set the
production CSP, which is acceptable locally. If it does not serve `.wasm`
as `application/wasm` on your machine, full-prover testing may need a
different static server; the OAuth flow itself does not depend on wasm.

Create the development OAuth app with:

- Homepage URL: `http://127.0.0.1:8000/`
- Callback URL: `http://127.0.0.1:8000/github-callback.html`

Run the development Worker:

```sh
cd support/oauth-worker
npm run dev
```

For local development, `.dev.vars` contains only the secret:

```text
GITHUB_CLIENT_SECRET=...
```

The dev environment in `wrangler.jsonc` supplies:

```text
GITHUB_CLIENT_ID=<development client id>
ALLOWED_ORIGIN=http://127.0.0.1:8000
REDIRECT_URI=http://127.0.0.1:8000/github-callback.html
```

Build the frontend with the local Worker URL:

```sh
cd support
npm run web:build:dev
```

`web:build:dev` uses `web:js:dev`, which defines
`__GITHUB_OAUTH_WORKER__` as `http://127.0.0.1:8787`, then builds the
callback, worker, and CSS. If you prefer a deployed development Worker,
point the define at that HTTPS URL instead and add the loopback origin to
its environment.

Caveats:

- `crypto.subtle` is available on `http://127.0.0.1:8000` because
  loopback is treated as a secure context.
- If you serve the repository root instead of `web/`, the callback path
  becomes `/web/github-callback.html`; update the OAuth app, the Worker
  `REDIRECT_URI`, and the dev define accordingly.
- The production Worker accepts only `https://abella-prover.org`, and the
  production OAuth app accepts only the production callback. Do not point
  a local page at either.

## 6. Security requirements

- **Client secret in static assets.** The secret exists only as a
  Cloudflare Worker secret. No secret in the repo, frontend bundle,
  callback page, or CI.
- **Authorization-code interception.** PKCE S256; the verifier stays in
  the main tab's memory. Codes are single-use and short-lived.
- **Login CSRF / account confusion.** Random `state`, one pending flow,
  exact match, 10-minute expiry. Validate the token with `/user` and show
  the account login.
- **Token theft via XSS.** Token in `sessionStorage` only; strict CSP; no
  third-party scripts; no token in URLs, DOM, logs, or errors.
- **CORS abuse.** Exact `ALLOWED_ORIGIN`, `Vary: Origin`, no wildcard, no
  credentials.
- **Open token-exchange proxy.** Redirect URI fixed by the Worker; origin
  allowlist; body and field limits; rate limit; PKCE.
- **Secret leakage through logs.** Never log request bodies, codes,
  verifiers, tokens, or `Authorization` headers. Log only request IDs and
  status codes.
- **Replay of the callback message.** `state` is single-use; clear the
  pending flow on success, error, timeout, or popup close. Ignore messages
  from other origins or sources.
- **Popup opener abuse.** Callback posts only to
  `window.location.origin`; main checks `event.origin` and `event.source`;
  no token is ever in the popup.
- **Broad OAuth scopes.** `public_repo` by default; `repo` only with an
  explicit checkbox and warning; PAT fallback for per-repository access.
- **Stale or revoked token.** Clear on 401; Disconnect; link to GitHub's
  authorized-apps settings.
- **Rate-limit or cost abuse.** Cloudflare rate-limit rule on the token
  route; 4 KiB body limit; 10-second upstream timeout.
- **Deployment header interference.** Verify COOP and CSP on the real
  origin; keep `connect-src` narrow and explicit.

Additional requirements:

- No token or code in `document.referrer`; the callback page sets
  `Referrer-Policy: no-referrer`.
- The Worker returns `Cache-Control: no-store` on every route.
- The Worker must not follow redirects from the token endpoint.
- The Worker must reject requests without an `Origin` header. A
  server-to-server request can spoof `Origin`, but it still needs a valid
  code and PKCE verifier.
- The frontend must not log the token, even at debug level.
- The OAuth app should be owned by a project-owned GitHub account or
  organization, not a personal account, so access survives maintainer
  changes.
- The client secret rotation procedure must be documented and rehearsed.

## 7. Implementation plan and deliverables

### Phase 0: local prerequisites and development app

This phase is local only. Do not touch `abella-prover.org`, its DNS, or
the production OAuth app yet. Those belong to Phase 5.

Tasks:

- Fix the local origin at `http://127.0.0.1:8000` and the local Worker at
  `http://127.0.0.1:8787`.
- Create the development OAuth App with the callback URL
  `http://127.0.0.1:8000/github-callback.html`.
- Record the development client ID and store the secret locally in
  `.dev.vars`, never in the repo.
- Confirm `wrangler dev` can reach GitHub's token endpoint from the
  development machine.
- Verify that `python3 -m http.server 8000 --bind 127.0.0.1` serves the
  `web/` tree and reaches the callback page.
- Confirm that `crypto.subtle` works on the loopback origin.

Deliverables:

- One registered development OAuth App.
- A local `.dev.vars` with the development secret.
- A short local-development note in the Worker README, with no secrets.

Exit criteria:

- A test authorization with the development app reaches
  `http://127.0.0.1:8000/github-callback.html` and shows `code` and
  `state` in the popup URL.
- No production hostname, DNS record, or production secret has been
  touched.

Implementation notes (2026-10-23):

- The public development client ID is recorded under `env.dev.vars` in
  `support/oauth-worker/wrangler.jsonc`. The client secret lives only in
  the gitignored `.dev.vars`.
- Wrangler 4.152.0 loads the plain `.dev.vars` file with
  `wrangler dev --env dev`; environment-specific `.dev.vars.<env>`
  files remain optional overrides. The development Worker keeps
  `.dev.vars`, which stays local.
- GitHub's callback now includes an `iss` query parameter in addition to
  `code` and `state`. The callback parser must ignore unknown parameters.
- An unknown client ID receives a JSON 404 from the token endpoint. A
  real development app returns `bad_verification_code` for a probe code,
  which is the useful connectivity and credential check.
- The Phase 0 authorization test reached the callback with a matching
  `state`; the code was not exchanged.

### Phase 1: Worker

Tasks:

- Create `support/oauth-worker/` with the package, tsconfig, Wrangler
  configuration, and README.
- Implement `GET /github/config`, `POST /github/token`, CORS, validation,
  upstream exchange, timeout, and error mapping.
- Add unit tests with a mocked `fetch`; no real GitHub calls.
- Exercise the Worker locally with `wrangler dev` and `curl` against the
  development OAuth app.
- Run a secret-leak audit of the built Worker bundle and response bodies.

Deliverables:

- Worker source and tests.
- `wrangler.jsonc` with `dev` and `production` environments.
- `.dev.vars.example` with placeholder values.
- Worker README covering deployment, secrets, rotation, and rate limits.
- CI job for Worker check and tests.

Exit criteria:

- `GET /github/config` works for the allowed origin and is rejected for
  another origin.
- `POST /github/token` exchanges a real development code with PKCE and
  returns only `token` and `scope`.
- The secret never appears in the response, logs, or bundle.
- Preflight and error cases are covered by tests.

Implementation notes (2026-10-23):

- Workerd rejects `redirect: "error"` for upstream `fetch`. The Worker
  uses `redirect: "manual"` and maps any 3xx response to 502, which
  preserves the no-follow rule.
- `wrangler dev --env dev` loads the plain `.dev.vars` file in
  Wrangler 4.152.0, so the development setup keeps the Phase 0 file
  name.
- A probe exchange through the local Worker reaches GitHub and maps
  `bad_verification_code` to a 400 with `invalid_code`, confirming
  upstream connectivity and credential handling without exposing a
  token.
- A real development code with PKCE exchanged successfully through the
  local Worker (HTTP 200); replaying the same code returned 400,
  confirming single-use behavior. The token was not written to the
  repository or logs.

### Phase 2: Frontend OAuth client and callback

Tasks:

- Add `github-oauth.ts` with PKCE, state, URL construction, config fetch,
  exchange, and token validation.
- Add `oauth-callback.ts` for the shared callback parser.
- Add `github-oauth-config.ts`.
- Add `github-callback.ts` and `web/github-callback.html`.
- Add `github-oauth.test.ts` and include it in `web:test`.
- Add the callback build entry and size budget.
- Update `.gitignore` for the callback HTML exception and generated
  callback JS.

Deliverables:

- OAuth client module and unit tests.
- Static callback page and its tiny bundle.
- Build and ignore updates.

Exit criteria:

- PKCE vectors, URL parameters, callback parsing, and message validation
  are covered by tests.
- The callback bundle stays under its gzip budget.
- A manual test with the dev app shows the popup posting `code` and
  `state` to the opener and closing.

Implementation notes (2026-10-23):

- The callback relay was exercised in Chromium: the opener received
  `{type, code, state}`, the query string was removed from the popup
  URL, and the popup closed. The real GitHub redirect path was verified
  in Phases 0 and 1; the full dialog flow follows in Phase 3.
- The callback bundle is 0.5 KiB gzip, below the 4 KiB budget.
- `web:js:dev` defines the loopback Worker URL; the production default
  is used when the define is absent.
- GitHub's `iss` parameter is ignored by the parser.

### Phase 3: Dialog and workspace integration

Tasks:

- Add the OAuth button, private-scope checkbox, PAT disclosure, notes, and
  revoke link to `web/index.html`.
- Add the pending-flow state, popup management, message handler, timeout,
  and popup-close handling to `main.ts`.
- Refactor the GitHub submit path into a shared token completion function.
- Resume connect and commit intents after OAuth.
- Add `/user` validation and account display.
- Clear tokens on 401 and update auth copy.
- Ensure public read-only loading still works without a token.
- Ensure the PAT path still works and is reachable when OAuth is hidden.

Deliverables:

- Updated dialog markup and styles.
- Updated `main.ts` and `github-auth.ts` plumbing.
- Updated `workspace-github.ts` error/copy changes if needed.
- New UI state handling for all failure modes.

Exit criteria:

- OAuth connect and commit both work end to end in a development
  deployment.
- Cancelling, closing the popup, blocking the popup, and a state mismatch
  all leave the app usable and the PAT path available.
- No token appears in the main page URL or history.

### Phase 4: Verification and documentation

Tasks:

- Run the manual end-to-end checklist in section 8.
- Run `npm run check`, `npm run web:test`, `npm run web:size`, and the
  Worker tests.
- Run the existing web smoke flow to catch regressions.
- Update `README_Web.md` with OAuth setup, Worker deployment, CSP, local
  development, and security notes.
- Update `support/oauth-worker/README.md` with secret rotation and rate
  limiting.
- Draft the `plans/abella-web/v11.md` note recording the OAuth sidequest
  and the changed authentication decision, but do not publish it until
  the production deployment succeeds. Do not edit v10 in place.

Deliverables:

- Passing checks and a completed manual checklist.
- Updated deployment documentation.
- A draft v11 note.

Exit criteria:

- All acceptance criteria in section 10 pass against a local development
  deployment.
- A maintainer other than the author can follow the documentation to run
  the local flow and prepare the production deployment.

### Phase 5: Production deployment

This is the only phase that touches `abella-prover.org` DNS, the
production OAuth app, or production secrets. Phases 0 through 4 can be
completed entirely against `127.0.0.1`.

Tasks:

- Create the production OAuth App with the exact callback URL
  `https://abella-prover.org/web/github-callback.html`.
- Confirm the production Worker hostname. The recommended value is
  `oauth.abella-prover.org`; the fallback is the `workers.dev` URL.
- Create the Cloudflare custom domain or DNS record for the Worker.
- Set `GITHUB_CLIENT_ID`, `ALLOWED_ORIGIN`, and `REDIRECT_URI` for the
  production environment, then set `GITHUB_CLIENT_SECRET` with
  `wrangler secret put`.
- Deploy the production Worker.
- Configure the Cloudflare rate-limit rule for `POST /github/token`.
- Verify `GET /github/config` with
  `Origin: https://abella-prover.org` and with a rejected origin.
- Add the Worker origin to the production CSP `connect-src`. Verify the
  callback page headers (`Cache-Control`, `Referrer-Policy`,
  `X-Frame-Options`/`frame-ancestors`) and the `/web/` COOP policy.
- Build the production static site with the chosen Worker URL (`make web`
  with the production default, or a build define for the `workers.dev`
  fallback), then publish it with `make publish-web` or the regular
  deployment procedure.
- Run the production smoke checks: public repository read, OAuth public
  scope, private-scope opt-in, commit, cancellation, blocked popup, and
  PAT fallback.
- Publish `plans/abella-web/v11.md` and add a row to
  `plans/abella-web/README.md`.
- Record the rollback check: make `/github/config` return 503 (or remove
  the Worker route) and confirm the UI falls back to PAT-only.

Deliverables:

- A deployed production Worker with a custom domain and rate limit.
- A production OAuth App with the exact callback URL.
- Updated production CSP/COOP/referrer configuration.
- The deployed static site at `https://abella-prover.org/web/`.
- Production smoke-test results and a verified rollback.
- The published v11 plan note and version-log row.

Exit criteria:

- `https://abella-prover.org/web/` loads with no CSP or console errors.
- `GET /github/config` succeeds only for the production origin.
- Sign-in, public read/write, private opt-in, commit, cancellation, and
  PAT fallback all work on the real origin.
- The callback page is served from the exact registered URL.
- No secret appears in the deployed assets or the repository.
- The rollback path hides OAuth and leaves the PAT path usable.
- The v11 plan note is published and `plans/abella-web/README.md` points
  to it.

### Deliverables summary

- **OAuth client and tests:** `support/ts/web/github-oauth.ts`,
  `support/ts/web/oauth-callback.ts`, `github-oauth.test.ts`.
- **Frontend config:** `support/ts/web/github-oauth-config.ts`.
- **Callback page:** `web/github-callback.html`,
  `support/ts/web/github-callback.ts`.
- **Dialog and flow integration:** `web/index.html`,
  `support/ts/web/main.ts`, `support/css/web.css`.
- **Token/auth plumbing:** `support/ts/web/github-auth.ts`,
  `support/ts/web/workspace-github.ts`.
- **Worker:** `support/oauth-worker/` (package, source, tests, Wrangler
  config, README).
- **Build and budgets:** `support/package.json`,
  `support/scripts/check-web-size.mjs`.
- **CI:** `.github/workflows/web.yml` or a new Worker workflow.
- **Repo hygiene:** `.gitignore`, `Makefile`.
- **Documentation:** `README_Web.md`, `support/oauth-worker/README.md`.
- **Plan bookkeeping:** `plans/abella-web/v11.md`,
  `plans/abella-web/README.md`.

## 8. Test plan

### 8.1 Frontend unit tests

Add `support/ts/web/github-oauth.test.ts` and include it in `web:test`.

Cover:

- base64url encoding has no `+`, `/`, or `=`;
- verifier length and character set;
- challenge matches an independently computed SHA-256 value;
- authorize URL contains `client_id`, `redirect_uri`, `scope`, `state`,
  `code_challenge`, and `code_challenge_method=S256`, and no secret;
- callback parsing for success, `access_denied`, missing code, and
  malformed input;
- state mismatch, stale state, and a second message for the same flow are
  rejected;
- messages from another origin or another source are ignored;
- exchange success saves the token and scope;
- exchange failure does not save a token;
- `/user` failure clears or rejects the token;
- commit intent calls `workspace.authorize` and then resumes the pending
  commit;
- connect intent calls the existing repository load path;
- a blocked popup reports an error and leaves the PAT path usable;
- a 401 from a later request clears the stored token.

Use fakes for `window.open`, `postMessage`, `sessionStorage`, `fetch`, and
the popup's `close` method. Do not require a real browser for these tests.

### 8.2 Worker unit tests

Add `support/oauth-worker/src/index.test.ts`.

Cover:

- config succeeds for the exact allowed origin;
- config is rejected for another origin, a missing origin, or a missing
  configuration;
- preflight response for allowed and disallowed origins;
- method rejection;
- malformed JSON, missing fields, and oversized bodies;
- token exchange sends the expected form fields, including
  `client_secret`, `code`, `redirect_uri`, and `code_verifier`;
- the response contains only `token` and `scope`;
- `refresh_token` is not forwarded even if GitHub returns one;
- GitHub 200 with an `error` field maps to a 400 with a safe message;
- GitHub 5xx and network failures map to 502 or 504;
- timeout behavior;
- `Cache-Control: no-store` and `X-Content-Type-Options: nosniff`;
- no secret or code appears in an error response.

Mock `globalThis.fetch` and pass a fake `env` object. No network access.

### 8.3 Manual end-to-end checklist

Use the development OAuth app and a development Worker. Repeat the
critical cases in Chromium and Firefox; add WebKit/Safari if available.

1. Load a public repository without a token. Confirm the existing
   read-only behavior is unchanged.
2. Open the GitHub dialog. Confirm the OAuth button appears, the PAT
   section is collapsed, and the Worker config request succeeds.
3. Sign in with the default `public_repo` scope. Confirm the popup opens,
   the callback closes it, the dialog shows the account login, and no
   token or code is in the main URL.
4. Load a public repository and commit a change with the OAuth token.
   Confirm the commit uses the existing atomic Git Data API path.
5. Try a private repository with the public-only token. Confirm the error
   offers "Reconnect with private repository access."
6. Reconnect with `repo`, load the private repository, and commit.
7. Cancel at GitHub. Confirm a clear message, no token saved, and a
   working PAT fallback.
8. Tamper with `state` in the callback URL. Confirm no exchange happens.
9. Block popups and press the OAuth button. Confirm the error tells the
   user to allow popups or use a token.
10. Close the popup before completing. Confirm the dialog recovers.
11. Revoke the app's access in GitHub settings, then try a request.
    Confirm 401 handling clears the token and prompts for reconnection.
12. Disconnect. Confirm the token is removed from `sessionStorage` and
    the workspace becomes non-writable until reconnected.
13. Reload the tab with a saved token. Confirm the token is restored in
    the same tab and OAuth is not required again.
14. Open the page in a fresh tab by typing the URL, not by duplicating
    the current tab. Confirm the token is not shared.
15. Check the browser console and network panel for CSP violations,
    token leakage, or unexpected origins.
16. Run the existing examples, zip, persistence, and commit smoke checks.

### 8.4 Regression checks

- `npm run check`
- `npm run web:test`
- `npm run web:size`
- `make web` (wasm backend)
- The existing web CI workflow
- `support/oauth-worker` check and tests

## 9. Rollout, operations, and rollback

### 9.1 Deployment order

This is the Phase 5 sequence. None of it is needed for local development.

1. Register the production OAuth app and configure the Worker secret.
2. Deploy the Worker to production.
3. Verify `GET /github/config` from the production origin.
4. Build and deploy the static site with the Worker URL in the CSP.
5. Verify the OAuth button appears and the PAT path still works.

Deploying the Worker first is safe: the old static page does not call it.
Deploying the static page with a missing or misconfigured Worker is also
safe because the OAuth button is hidden when config fails.

### 9.2 Feature availability

There is no separate feature flag. The `/github/config` endpoint is the
flag:

- configured and reachable -> OAuth button visible;
- missing, failing, or rejected -> OAuth hidden, PAT available.

This gives a natural rollback: disable the Worker route or remove its
configuration, and the static site reverts to PAT-only behavior without a
redeploy.

### 9.3 Monitoring

- Cloudflare Worker analytics: request count, error rate, CPU time.
- Rate-limit rule hit count.
- No request-body logging.
- A small set of status-coded logs is enough to diagnose configuration
  and upstream failures.
- Alert on a sustained 5xx rate, not on individual user cancellations.

### 9.4 Secret rotation

1. Generate a new client secret in the GitHub OAuth app.
2. Run `wrangler secret put GITHUB_CLIENT_SECRET --env production`.
3. Verify a new sign-in works.
4. Invalidate the old secret in GitHub if the UI offers that step.
5. If the secret was exposed, review Worker logs for unusual traffic and
   revoke affected user tokens through GitHub's authorized-app settings.

### 9.5 Cost

The Worker runs on Cloudflare's free or low-cost plan. The flow makes one
config request per dialog open and one token exchange per sign-in. This is
far below the free-tier request limits for a documentation/prover site.
The main operational cost is maintainer attention to OAuth app ownership,
secret rotation, and CSP changes.

### 9.6 Rollback

- Hide the OAuth button by making `/github/config` return 503 or by
  removing the Worker route.
- Keep the PAT path in the UI at all times.
- Revert the static deployment if the callback page or CSP breaks
  navigation.
- No database or session state needs cleanup.

## 10. Acceptance criteria

- A user can sign in with GitHub from the GitHub dialog using a popup.
- The popup callback page posts only `code` and `state` to the opener; it
  never receives or stores a token.
- The Worker exchanges the code with PKCE and a client secret that exists
  only in Cloudflare.
- `state` and PKCE are verified; a mismatch or replay does not exchange a
  code.
- The token is validated with `/user` and stored only in `sessionStorage`.
- No token or client secret appears in any URL, `localStorage`, logs,
  error text, or the built static assets. The authorization code appears
  only in the short-lived callback popup URL, is never exchanged there,
  and is removed with `history.replaceState` before the popup closes.
- Public repository reads still work without a token.
- OAuth tokens work for public and private repository reads and for
  commits through the existing `GitHubWorkspace` path.
- `public_repo` is the default; `repo` is an explicit opt-in with a clear
  warning and a PAT alternative.
- Cancelled login, blocked popup, closed popup, state mismatch, Worker
  failure, insufficient scope, and revoked token all leave the app usable
  and show an actionable message.
- The PAT path remains fully functional and is reachable when OAuth is
  unavailable.
- CORS rejects other origins; preflight works; rate limiting is
  configured.
- The deployed CSP allows the Worker origin and the GitHub API origins,
  with no console violations.
- The callback HTML is tracked, the generated callback JS is ignored, and
  the callback bundle has a size budget.
- Frontend unit tests, Worker unit tests, type checks, bundle-size checks,
  and the existing web smoke flow pass.
- `README_Web.md` and the Worker README document setup, deployment,
  rotation, and rollback.
- A v11 plan note records the completed sidequest and the changed
  authentication decision.

## 11. Risks and mitigations

- **Popups are blocked or the browser drops the opener.** Detect the
  blocked popup, show a clear error, keep the PAT path. Verify COOP
  headers on the deployed origin.
- **A full-page redirect would lose unsaved work.** Use the popup. If a
  redirect fallback is ever needed, it must first persist and restore the
  workspace and pending commit; that is a separate design.
- **OAuth scopes are broader than fine-grained PATs.** Default to
  `public_repo`; require an explicit opt-in for `repo`; keep the PAT path;
  explain the difference in the dialog.
- **Worker is abused as a token exchange service.** Exact origin, fixed
  redirect URI, PKCE, body limits, rate limiting, no logging of secrets.
- **Client secret leaks through a repo or build.** Secret only in
  Cloudflare; no secret in `.dev.vars.example`, CI, or the frontend; audit
  built assets.
- **Callback URL or redirect URI mismatch.** Separate dev and prod apps;
  exact callback URLs; Worker config is the source of truth;
  `redirect_uri_mismatch` produces a configuration error.
- **Token theft through XSS.** `sessionStorage`, strict CSP, no
  third-party scripts, no token in DOM or logs, Disconnect, revocation
  link.
- **Stale token after revocation.** Validate with `/user`; clear on 401;
  prompt to reconnect.
- **Account mixing.** Validate the token with `/user`, show the login, and
  make the active account visible when writing.
- **State lost on reload.** Store the pending flow in memory; a reload
  aborts safely; the user retries.
- **Worker or GitHub outage.** OAuth button hidden or an actionable error;
  PAT fallback; no data loss.
- **OAuth app ownership changes.** Use a project-owned account or
  organization; document the owner and recovery path.
- **CI cannot test a real OAuth round trip.** Unit tests mock all network
  I/O; keep a documented manual checklist with a development OAuth app.
- **CSP or COOP regression in deployment.** Add both to the deployment
  checklist and test on the real origin, not only on localhost.
- **Bundle growth.** Keep the OAuth module small, add a callback budget,
  and verify the existing initial-bundle budget.

## 12. Out of scope and future work

- **GitHub App with fine-grained permissions.** This is the better
  long-term security model: repository-scoped permissions, short-lived
  user tokens, and installation management. It requires a GitHub App,
  installation handling, and a different token exchange. It should be a
  separate plan if the broad OAuth scopes become a problem.
- **Device flow.** It needs no client secret and could run on a purely
  static site, but the user must copy a code into GitHub. It is a useful
  fallback if the Worker is unacceptable.
- **Expiring tokens and refresh tokens.** Enable only with a deliberate
  refresh implementation, a safe refresh-token storage policy, and tests
  for expiry while the tab is open.
- **Other providers.** GitLab and Gitea can use OAuth/PKCE; Dropbox uses
  PKCE. They are separate provider plans.
- **Persisted OAuth sessions across tabs.** Not planned. The token remains
  per-tab in `sessionStorage`.
- **A full-page redirect fallback.** Not planned for v1 because of the
  workspace-state loss described above.

## 13. Decisions to confirm

This plan takes the following positions. The first two affect the
implementation and should be settled before Phase 0. The last two can wait
until Phase 5 because they concern production deployment only.

Before Phase 0:

1. **Default scope:** `public_repo` with an explicit `repo` opt-in is
   recommended. The sketch's always-`repo` behavior is simpler but grants
   account-wide private repository access to every user who signs in.
2. **Popup flow:** recommended, because it preserves the in-memory
   workspace and pending commit. A full-page redirect is not part of this
   plan.

Before Phase 5:

3. **Worker hostname:** `https://oauth.abella-prover.org` is recommended.
   The fallback is the Cloudflare `workers.dev` URL. The chosen URL goes
   into the production CSP and the production frontend build.
4. **OAuth app ownership:** a project-owned account or organization is
   recommended over a personal account, so the app and its secret survive
   maintainer changes.
