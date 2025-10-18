# Changelog

All notable changes to this project will be documented in this file.

## rustsat-v0.7.4 - 2025-10-18

[b0343ca](b0343ca8feb853254afb02f3ee0f4fe480687417)...[547959f](547959f824fc1591812b2f24a7658ef36921e54e)

### Documentation

- Generate changelog ([547959f](547959f824fc1591812b2f24a7658ef36921e54e))

### Miscellaneous Tasks

- Switch CI to nix ([7c73dcf](7c73dcfdb7358ed64a1b70442daeb92a6fa39621))
- Update to pyo3 0.26.0 ([3167083](3167083835cd27593339989345429876146c9231))
- Include keep-sorted formatter ([46e505c](46e505cca3e50b7743c47288b2fb2610da3f1952))

## rustsat-v0.7.0 - 2025-04-03

[b5b2b3f](b5b2b3fd11bbe5f334351f256e01d21041c43605)...[db3a792](db3a792c565ef9b032819d484c5236f7dbc446d0)

### Bug Fixes

- Update patch updates to 0.23.5 (#288) ([56d327e](56d327e1b3973db0a52504efb6bc5a81694a9b89)), Co-authored-by:renovate[bot] <29139614+renovate[bot]@users.noreply.github.com>

### Documentation

- Update shield style ([0a79def](0a79def179185332997d58471153f45cc775ae84))

### Features

- Include bimander encoding ([fe9573a](fe9573acbb3201d1f674431a50dab247132761f3))
- Include lower bounding totalizer ([9ca396c](9ca396c1dfeff295233e4f49a76bdd4b00dbe5d0))

### Miscellaneous Tasks

- Update PyO3 to 0.24.0 ([85d4970](85d4970899b71599300fd72acbe9fb9c02d99a8c))
- Force synced versions via workspace ([3ca5f43](3ca5f43c8843aa61ef584da44c545e79a3d0a067))
- Remove deprecated CI badges ([72f4573](72f4573827bf51d9f3a02b14c92edab68417d905))
- [**breaking**] Code spell-checking ([e269ac1](e269ac17b3d5693081f553e5e7d40ad7959c2d44))
- Release (#334) ([db3a792](db3a792c565ef9b032819d484c5236f7dbc446d0)), resolves #269

* docs: update changelog

---------, Co-authored-by:rustsat-release-plz-bot[bot] <174992831+rustsat-release-plz-bot[bot]@users.noreply.github.com>, Co-authored-by:Christoph Jabs <christoph.jabs@helsinki.fi>

### Refactor

- [**breaking**] Don't use `anyhow` in encoding API ([1172825](117282510d8be4a05940c0913323d5ff8172d1fb))
- [**breaking**] Remove non-db totalizer encodings ([8392fec](8392fec14fb3e9462e270fe229f14dc0c62e0a1b))

## rustsat-v0.6.4 - 2025-02-19

[91a4161](91a4161bc7a7b8f4d4998a46ce51f6449055b214)...[b5b2b3f](b5b2b3fd11bbe5f334351f256e01d21041c43605)

### Bug Fixes

- Stricter `pyproject.toml` requirements ([ef91128](ef911281d1b39214e3720725f58397ac1e4c3b4f))
- Specify `__all__` in python stubs ([b50a9be](b50a9be90324ad3294ea4d49f3ba954220625c2d))
- Update patch updates (#241) ([e0bb289](e0bb2896702d4df14f322a427fe8515e838efdb9)), Co-authored-by:renovate[bot] <29139614+renovate[bot]@users.noreply.github.com>
- Use fxhash ([1828eef](1828eefd4f53e06f1e525e228452b34cb18836fb))

### Miscellaneous Tasks

- Manual release tasks ([b5b2b3f](b5b2b3fd11bbe5f334351f256e01d21041c43605))

## rustsat-v0.6.3 - 2024-12-20

[f58b188](f58b188fa876291f717b919c6b2934f6761da2ce)...[91a4161](91a4161bc7a7b8f4d4998a46ce51f6449055b214)

### Bug Fixes

- Confusing parameter names ([ea5f1b8](ea5f1b8c4086dfc23d918865046fe7e1c7fdbf09))
- Extend stubs to properly include submodules ([2f7ab25](2f7ab25cdf9f0c43152abc372e7cf253fefd9490))

### Documentation

- Include type annotations ([e514a1b](e514a1bb47cec7dfdb0704d08e7bb23aa9bb7ab1))

### Features

- Include `BinaryAdder` encoding ([48290ba](48290ba346cf1e9df06b02699dc05d451ce382cb))
- Restructure python API ([4c3cd72](4c3cd72d82ae30b3c678e9dddaddffccbf7753ba))
- Include at-most-one encodings ([d258eb1](d258eb1749efb133727bb08439fddf7b3906e16c))

### Miscellaneous Tasks

- Format python example ([8b9b2ef](8b9b2efa4f7cd35b0c25bdfdfdea82da414668c9))
- Release ([91a4161](91a4161bc7a7b8f4d4998a46ce51f6449055b214))

### Refactor

- Simplify pyapi with macros ([b19eb6f](b19eb6f4260b051b59adc1aebe5f9bd7c9e49f59))

## rustsat-v0.6.2 - 2024-12-13

[9c2bcbf](9c2bcbfd09b956624cedd8818e127e69f01c4fd3)...[f58b188](f58b188fa876291f717b919c6b2934f6761da2ce)

### Miscellaneous Tasks

- Spellchecking documentation ([11a1229](11a12291fa16fd847baacb8450bc8bb236afee44))
- Cleanup file endings and trailing whitespace ([9682aaa](9682aaa824830d0475a7adaac811e36f787f2e37))
- Release ([f58b188](f58b188fa876291f717b919c6b2934f6761da2ce))

## rustsat-v0.6.1 - 2024-10-16

[ff1a3d6](ff1a3d6fea12e8d16aa97678c72b91f39eabe7bf)...[9c2bcbf](9c2bcbfd09b956624cedd8818e127e69f01c4fd3)

### Miscellaneous Tasks

- Move main crate to project root ([74e8408](74e84085a5f8b6fb84c72416e0c42fa8f750a104))
- Pedantic clippy ([fae9eef](fae9eefdf024ebe05b42e3bdf13d84e8139d07bc))
- [**breaking**] Breaking clippy suggestions ([55a60f5](55a60f538e01c220f061223c18d65fd4836e3fe6))
- Update to PyO3 0.22.0 ([03e888b](03e888bacb4214703be4def8e73a5d1f9e2fce8f))
- Update dependencies ([971b258](971b258d21d96f909230dec86e78bd849ea328ab))
- Bump pyo3 from 0.22.3 to 0.22.4 ([40cc9db](40cc9db0d338cc9db1285fd4bcbf76f3b3f1689c)), Signed-off-by:dependabot[bot] <support@github.com>
- Bump pyo3 from 0.22.4 to 0.22.5 ([083506a](083506afb610580e0f3cb4579680558e0d363b12)), Signed-off-by:dependabot[bot] <support@github.com>
- Manual release tasks ([4ea4fa6](4ea4fa64e36fbed65289f206a19176122e0d896f))
- Manual release tasks ([9c2bcbf](9c2bcbfd09b956624cedd8818e127e69f01c4fd3))

## rustsat-v0.5.1 - 2024-06-12

[f8d6dd8](f8d6dd8b8bd837ece694d2ad89bf2e28bd6966cb)...[ff1a3d6](ff1a3d6fea12e8d16aa97678c72b91f39eabe7bf)

### Documentation

- Add missing documentation ([50990b7](50990b7224bcaef4ecd19823433fd528eb4a0806))

### Features

- Catch memory outs in clause collector ([b0ab426](b0ab426e545c85f11a66b8098c8171d776a95516))

### Miscellaneous Tasks

- Release ([3568fac](3568fac30dc97ece0e4985f73e9e205038cf744e)), Signed-off-by:Christoph <98587286+chrjabs@users.noreply.github.com>
- Release ([ff1a3d6](ff1a3d6fea12e8d16aa97678c72b91f39eabe7bf))

### Refactor

- Factor out Python API ([bd5cbea](bd5cbea23b8d1d9b36956b4d0d3abc97d782eae4))

<!-- generated by git-cliff -->
