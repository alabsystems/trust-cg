# Security policy

trust-cg v0.1.0 is alpha research software and is not approved for production,
safety-critical, or security-critical use. Correctness and robustness bugs are
still security-relevant to the project, especially when they can cause silent
wrong code, bypass a fail-closed gate, forge or misbind evidence, or execute
untrusted input unsafely.

## Supported versions

Only the latest public 0.x release receives security fixes. Development
snapshots and older 0.x releases may be used to reproduce a report but are not
maintained as separate security branches.

## Reporting a vulnerability

Do not open a public issue for an unpatched vulnerability. Email
`andrewyates.name@gmail.com` with the subject `trust-cg security report` and
include:

- the affected revision and target;
- impact and the trust boundary crossed;
- a minimal reproducer or artifact, if safe to share;
- whether the issue is already public; and
- a secure way to continue the conversation if email is insufficient.

You should receive an acknowledgement within seven days. The project will
coordinate reproduction, scope, remediation, and disclosure. Please avoid
accessing data or systems you do not own while investigating.

Ordinary crashes, unsupported inputs, and documented incompleteness can be
reported through the public issue tracker unless they expose a security
boundary bypass.
