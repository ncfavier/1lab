{ # Is this a nix-shell invocation?
  inNixShell ? false
  # Do we want the full Agda package for interactive use? Set to false in CI
, interactive ? true
, system ? builtins.currentSystem
}:
let
  pkgs = import ./support/nix/nixpkgs.nix { inherit system; };
  inherit (pkgs) lib;

  our-ghc = pkgs.labHaskellPackages.ghcWithPackages (ps: with ps; ([
    shake directory tagsoup
    text containers uri-encode
    process aeson Agda pandoc SHA
    fsnotify
  ] ++ (if interactive then [ haskell-language-server ] else [])));

  our-texlive = pkgs.texlive.combine {
    inherit (pkgs.texlive)
      collection-basic
      collection-latex
      xcolor
      preview
      pgf tikz-cd braids
      mathpazo
      varwidth xkeyval standalone;
  };

  shakefile = pkgs.callPackage ./support/nix/build-shake.nix {
    inherit our-ghc;
    name = "1lab-shake";
    main = "Main.hs";
  };

  sort-imports = let
    script = builtins.readFile support/sort-imports.hs;
    # Extract the list of dependencies from the stack shebang comment.
    deps = lib.concatLists (lib.filter (x: x != null)
      (map (builtins.match ".*--package +([^[:space:]]*).*")
        (lib.splitString "\n" script)));
  in pkgs.writers.writeHaskellBin "sort-imports" {
    ghc = pkgs.labHaskellPackages.ghc;
    libraries = lib.attrVals deps pkgs.labHaskellPackages;
  } script;

  deps = with pkgs; [
    # For driving the compilation:
    shakefile

    # For building the text and maths:
    gitMinimal nodePackages.sass

    # For building diagrams:
    poppler_utils our-texlive
  ] ++ (if interactive then [
    our-ghc
    sort-imports
  ] else [
    labHaskellPackages.Agda.data
    labHaskellPackages.pandoc.data
  ]);

  _1lab-agda = (pkgs.agdaPackages.override {
    inherit (pkgs.labHaskellPackages) Agda;
  }).mkDerivation {
    pname = "1lab";
    version = "unstable";
    src = ./.;
    postPatch = ''
      # We don't need anything in support; avoid installing LICENSE.agda
      rm -rf support

      # Remove verbosity options as they make Agda take longer and use more memory.
      shopt -s globstar extglob
      files=(src/**/*.@(agda|lagda.md))
      sed -Ei '/OPTIONS/s/ -v ?[^ #]+//g' "''${files[@]}"

      # Generate all-pages manually instead of building the build script.
      mkdir -p _build
      for f in "''${files[@]}"; do
        f=''${f#src/} f=''${f%%.*} f=''${f//\//.}
        echo "open import $f"
      done > _build/all-pages.agda
    '';
    libraryName = "1lab";
    libraryFile = "1lab.agda-lib";
    everythingFile = "_build/all-pages.agda";
    meta = {};
  };
in
  pkgs.stdenv.mkDerivation rec {
    name = "1lab";

    src = if inNixShell then null else
      with pkgs.nix-gitignore; gitignoreFilterSourcePure (_: _: true) [
        # Keep .git around for extracting page authors
        (compileRecursiveGitignore ./.)
        ".github"
      ] ./.;

    nativeBuildInputs = deps;

    shellHook = ''
      export out=_build/site
    '';

    LANG = "C.UTF-8";
    buildPhase = ''
      1lab-shake all -j
    '';

    installPhase = ''
      # Copy our build artifacts
      mkdir -p $out
      cp -Lrvf _build/html/* $out

      # Copy KaTeX CSS and fonts
      mkdir -p $out/css
      cp -Lrvf --no-preserve=mode ${pkgs.nodePackages.katex}/lib/node_modules/katex/dist/{katex.min.css,fonts} $out/css/
      mkdir -p $out/static/ttf
      cp -Lrvf --no-preserve=mode ${pkgs.julia-mono}/share/fonts/truetype/JuliaMono-Regular.ttf $out/static/ttf/julia-mono.ttf
    '';

    passthru = {
      inherit deps shakefile sort-imports _1lab-agda;
      texlive = our-texlive;
      ghc = our-ghc;
    };
  }
