#!/usr/bin/env bash
# Compiles the prover and the ILTP harness into build/, the same way the Dockerfile does
# (javac, ISO-8859-1 sources, the AspectJ-only files excluded). Output: build/classes and
# build/classpath.txt, which the run scripts read.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# jdom2 is used by util.XMLViewer / main.tableau.RulesUsage and is not bundled in the repo.
mkdir -p kems.export/lib/extra
if [ ! -f kems.export/lib/extra/jdom2-2.0.6.jar ]; then
  echo "fetching jdom2 ..." >&2
  curl -fsSL https://repo1.maven.org/maven2/org/jdom/jdom2/2.0.6/jdom2-2.0.6.jar \
       -o kems.export/lib/extra/jdom2-2.0.6.jar
fi

CP="$(ls "$ROOT"/kems.export/lib/ext/*.jar "$ROOT"/kems.export/lib/generated/*.jar "$ROOT"/kems.export/lib/extra/*.jar | tr '\n' ':')"
rm -rf build/classes && mkdir -p build/classes
find kems.prover/src kems.prover/tests/logicalSystems/ipl -name "*.java" \
     -not -name "*Aspect.java" -not -name "ProofTreeSize.java" -not -name "MemoryUsageTracker.java" \
     -not -name "ProverThreadAspect.java" -not -name "Complexity.java" \
     -not -name "*Test.java" -not -name "MockSimpleStrategy.java" \
     > build/sources.txt
javac -encoding ISO-8859-1 --release 17 -d build/classes -cp "$CP" -Xlint:none -nowarn -proc:none @build/sources.txt
(cd kems.prover/src && find . -type f \( -name "*.properties" -o -name "*.xml" -o -name "*.dtd" \) \
   -exec sh -c 'mkdir -p "'"$ROOT"'/build/classes/$(dirname "$1")" && cp "$1" "'"$ROOT"'/build/classes/$1"' _ {} \;)
echo "$ROOT/build/classes:$CP" > build/classpath.txt
echo "built: $(find build/classes -name '*.class' | wc -l | tr -d ' ') classes" >&2
