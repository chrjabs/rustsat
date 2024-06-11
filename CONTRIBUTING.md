# RustSAT Contribution Guidelines

By contributing to RustSAT you agree to your work being published under the
[Licence of the project](https://github.com/chrjabs/rustsat/blob/main/LICENSE).

In a possible future publication related to RustSAT, the [contributors on
GitHub](https://github.com/chrjabs/rustsat/graphs/contributors) will be
acknowledged, but authorship remains with the maintainers of the project.

Pull requests with non-breaking changes should be against the
[`main`](https://github.com/chrjabs/rustsat/tree/main) branch. If the PR
contains breaking changes, it should be against the
[`next-major`](https://github.com/chrjabs/rustsat/tree/next-major) branch.

Before contributing, kindly go through the following checklist:

- Format code with `rustfmt` / `cargo fmt --all`. If this is not true, the
  automatic PR checks will fail.
- Name commits following [conventional
  commits](https://www.conventionalcommits.org/en/v1.0.0/#summary). Mainly,
  commits containing new features should start with `feat:`, commits
  containing bugfixes should start with `fix:`, and documentation-related
  commits should start with `docs:`. This makes automatic changelog compilation a
  lot easier.
- Write thorough documentation for new features. This documentation is
  automatically published to [docs.rs](https://docs.rs) upon release.
- Make sure the test suite passes locally. The automatic PR checks will run the
  test suite on a variety of different platforms.
- Add new test for new features or tests that would have caught bugs you fixed.
  If this is not possible, explain why.
