# Changelog

All notable changes to this project will be documented in this file.

## Unreleased

[b0343ca](b0343ca8feb853254afb02f3ee0f4fe480687417)...[66eafcd](66eafcd671099d2c66b2abb607176c925ed426d3)

### Miscellaneous Tasks

- Include keep-sorted formatter ([46e505c](46e505cca3e50b7743c47288b2fb2610da3f1952))
- Update version in header ([66eafcd](66eafcd671099d2c66b2abb607176c925ed426d3))

### Refactor

- Clearly mark internal features ([bbba25f](bbba25f4fbca47839ca3d0b00ee1a89976ba05f2))

## rustsat-v0.7.3 - 2025-08-07

[3f0fd8d](3f0fd8db3170dc92059e08bd7a6e6b6be8de7bce)...[b0343ca](b0343ca8feb853254afb02f3ee0f4fe480687417)

### Bug Fixes

- Totdb only reserve variables the connection needs (#435) ([8f0f2f3](8f0f2f3d156d45456ef5a443e136224f24211485)), fixes #165

### Miscellaneous Tasks

- Setup treefmt and format ([86e9096](86e909606373f42c203f88b1485095ae5d53f9b9))
- Clippy ([d959a33](d959a3366380a48b9ca00a4ede6b386f26f8dd25))
- Release (#402) ([b0343ca](b0343ca8feb853254afb02f3ee0f4fe480687417)), Co-authored-by:rustsat-release-plz-bot[bot] <174992831+rustsat-release-plz-bot[bot]@users.noreply.github.com>, Co-authored-by:Christoph Jabs <christoph.jabs@helsinki.fi>

## rustsat-v0.7.2 - 2025-05-30

[ab11fda](ab11fdaab1892b70f8d55a847033cb40e98300c1)...[3f0fd8d](3f0fd8db3170dc92059e08bd7a6e6b6be8de7bce)

### Miscellaneous Tasks

- Release (#370) ([3f0fd8d](3f0fd8db3170dc92059e08bd7a6e6b6be8de7bce)), Co-authored-by:rustsat-release-plz-bot[bot] <174992831+rustsat-release-plz-bot[bot]@users.noreply.github.com>, Co-authored-by:Christoph Jabs <christoph.jabs@helsinki.fi>

## rustsat-v0.7.1 - 2025-05-01

[db3a792](db3a792c565ef9b032819d484c5236f7dbc446d0)...[ab11fda](ab11fdaab1892b70f8d55a847033cb40e98300c1)

### Miscellaneous Tasks

- Don't generate header at build time ([0bb6d3d](0bb6d3d34c6f895fdca818abeeb3a7a83aa3095d))
- Codegen tool for generating bindings ([0fa496a](0fa496a6fd03398968fdf66f95409e8347077234))
- Add `publish = false` where appropriate (#358) ([6fbadf7](6fbadf7115cc481304f74e9797b690fcf24e7105))
- Update rust version ([2855770](2855770174d1a521d20c13ba5343e0d53699c718))
- Release (#350) ([ab11fda](ab11fdaab1892b70f8d55a847033cb40e98300c1)), Co-authored-by:rustsat-release-plz-bot[bot] <174992831+rustsat-release-plz-bot[bot]@users.noreply.github.com>, Co-authored-by:Christoph Jabs <christoph.jabs@helsinki.fi>

### Testing

- C tests with custom harness ([3e11ab4](3e11ab496a56e4b9334364b90c2ab28336d09570))

## rustsat-v0.7.0 - 2025-04-03

[b5b2b3f](b5b2b3fd11bbe5f334351f256e01d21041c43605)...[db3a792](db3a792c565ef9b032819d484c5236f7dbc446d0)

### Documentation

- Update shield style ([0a79def](0a79def179185332997d58471153f45cc775ae84))

### Features

- Include at-most-one encodings ([7458596](7458596ebb559afa0ee9d1d15ed4cd8349e49f11))
- Lower bounding totalizers ([cd8a6d0](cd8a6d04a5778b0f6d1ab272f8c4087ec9e71547))

### Miscellaneous Tasks

- Cargo clippy ([63a99fb](63a99fb32315fafafbd95d8a9f366302eb15259f))
- Force synced versions via workspace ([3ca5f43](3ca5f43c8843aa61ef584da44c545e79a3d0a067))
- Remove deprecated CI badges ([72f4573](72f4573827bf51d9f3a02b14c92edab68417d905))
- Don't sort functions ([896129d](896129d9ce185adb86af645f8e003db82ded9e52))
- Cleanup ([05aefb7](05aefb791ec6830da4f68df680ff8098c88ddf9e))
- Release (#278) ([2e4dc23](2e4dc23e25aac9b4d01282861a938b34d58fa0a6)), Co-authored-by:rustsat-release-plz-bot[bot] <174992831+rustsat-release-plz-bot[bot]@users.noreply.github.com>, Co-authored-by:Christoph Jabs <christoph.jabs@helsinki.fi>
- Release (#326) ([a9d2143](a9d214376ee39537f3c591425983e8de60fd5ddd)), Co-authored-by:rustsat-release-plz-bot[bot] <174992831+rustsat-release-plz-bot[bot]@users.noreply.github.com>
- Release (#334) ([db3a792](db3a792c565ef9b032819d484c5236f7dbc446d0)), resolves #269

* docs: update changelog

---------, Co-authored-by:rustsat-release-plz-bot[bot] <174992831+rustsat-release-plz-bot[bot]@users.noreply.github.com>, Co-authored-by:Christoph Jabs <christoph.jabs@helsinki.fi>

### Refactor

- [**breaking**] Don't use `anyhow` in encoding API ([1172825](117282510d8be4a05940c0913323d5ff8172d1fb))
- [**breaking**] Remove non-db totalizer encodings ([8392fec](8392fec14fb3e9462e270fe229f14dc0c62e0a1b))

## rustsat-v0.6.4 - 2025-02-19

[91a4161](91a4161bc7a7b8f4d4998a46ce51f6449055b214)...[b5b2b3f](b5b2b3fd11bbe5f334351f256e01d21041c43605)

### Bug Fixes

- Use fxhash ([1828eef](1828eefd4f53e06f1e525e228452b34cb18836fb))

### Miscellaneous Tasks

- Manual release tasks ([b5b2b3f](b5b2b3fd11bbe5f334351f256e01d21041c43605))

## rustsat-v0.6.3 - 2024-12-20

[f58b188](f58b188fa876291f717b919c6b2934f6761da2ce)...[91a4161](91a4161bc7a7b8f4d4998a46ce51f6449055b214)

### Miscellaneous Tasks

- Release ([91a4161](91a4161bc7a7b8f4d4998a46ce51f6449055b214))

## rustsat-v0.6.2 - 2024-12-13

[9c2bcbf](9c2bcbfd09b956624cedd8818e127e69f01c4fd3)...[f58b188](f58b188fa876291f717b919c6b2934f6761da2ce)

### Bug Fixes

- Returnvalue of c header check ([940035b](940035b264a521496d0b8a834d59814c27bf3984))

### Documentation

- Mention panic cases ([5ebfab7](5ebfab7e28e44398cc3bb38150531b828092d63f))
- Improve documentation ([b0d1587](b0d1587620b511fb4a6647240c3b2d8cf1a5e93a))

### Features

- C-API for binary adder encoding ([a68f6cf](a68f6cfa842528f20b374bcbc16139daecbe270c))
- Expose `<enc>_reserve` ([a07fe96](a07fe96f327ce7232984659826f47c2bf3b3ef93))
- Include rustsat version in header ([25bcc7c](25bcc7cae4c338b3fdfba2188b7519290b99afa0))

### Miscellaneous Tasks

- Spellchecking documentation ([11a1229](11a12291fa16fd847baacb8450bc8bb236afee44))
- Cleanup file endings and trailing whitespace ([9682aaa](9682aaa824830d0475a7adaac811e36f787f2e37))
- Release ([f58b188](f58b188fa876291f717b919c6b2934f6761da2ce))

### Testing

- Assert against errors ([87f533c](87f533c7f1883d79a0523370274ef3dde16dff30))

## rustsat-v0.6.1 - 2024-10-16

[ff1a3d6](ff1a3d6fea12e8d16aa97678c72b91f39eabe7bf)...[9c2bcbf](9c2bcbfd09b956624cedd8818e127e69f01c4fd3)

### Bug Fixes

- Use `cargo:` syntax for backwards compat ([6dae65c](6dae65c288445416e6e162e5a7e337598dad3f54))

### Documentation

- Fix ambiguous links ([19b29f8](19b29f8b2f94a1d5e4fda941c759e6e9b5152458))

### Features

- Add generalized totalizer to capi ([fcb3330](fcb333033b6b1c93d0cacfd067b99c23d620052f))

### Miscellaneous Tasks

- Move main crate to project root ([74e8408](74e84085a5f8b6fb84c72416e0c42fa8f750a104))
- Pedantic clippy ([fae9eef](fae9eefdf024ebe05b42e3bdf13d84e8139d07bc))
- Clippy with most-recent nightly ([432d940](432d9401710597803fba3e3e5204f16e9853fc6e))
- Update dependencies ([971b258](971b258d21d96f909230dec86e78bd849ea328ab))
- Set up nix dev shell and tools package ([a7e26f2](a7e26f20594f5d7486ae6cf902b2459084172394))
- Manual release tasks ([4ea4fa6](4ea4fa64e36fbed65289f206a19176122e0d896f))
- Manual release tasks ([9c2bcbf](9c2bcbfd09b956624cedd8818e127e69f01c4fd3))

### Refactor

- Simplify pointer handling in c-api ([bcbab4b](bcbab4b3cd18ba5449f407e039f6df70cfe47874))
- Split capi into different files ([f519ee7](f519ee7e3e2c994843f14dfde5c9b044800a3221))

## rustsat-v0.5.1 - 2024-06-12

[f8d6dd8](f8d6dd8b8bd837ece694d2ad89bf2e28bd6966cb)...[ff1a3d6](ff1a3d6fea12e8d16aa97678c72b91f39eabe7bf)

### Documentation

- Update readmes ([5b26348](5b26348157cca72f64fad99f90640a8813482d7d))
- Improve dpw documentation ([d65a0e0](d65a0e0d154ac4d802a99a3f036c6c518a027591))

### Features

- Catch memory outs in clause collector ([b0ab426](b0ab426e545c85f11a66b8098c8171d776a95516))
- Incremental precision in DPW ([09e6264](09e62646bf9ebb27843efe11bd63490d616409dd))

### Miscellaneous Tasks

- Cleanup capi examples ([0fb0e12](0fb0e12a88d43ecdad6a6c7fca26fcb5297682bf))
- Release ([3568fac](3568fac30dc97ece0e4985f73e9e205038cf744e)), Signed-off-by:Christoph <98587286+chrjabs@users.noreply.github.com>
- Release ([ff1a3d6](ff1a3d6fea12e8d16aa97678c72b91f39eabe7bf))

### Refactor

- Factor out C-API ([1ce81bd](1ce81bd48611c796711d8bbeaa23a5dadc520215))

### Build

- Cleanup build script ([5c5de75](5c5de75bb9bacb9590df4eef92cf47396cf1d171))

<!-- generated by git-cliff -->
