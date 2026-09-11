# =============================================================================
# IPL KE-tableau Web Server — multi-stage Docker build
# =============================================================================
# Compiles the existing IntelliJ project (kems.prover/src) with the system's
# javac and packages the resulting classes plus the bundled library jars in
# a minimal JRE runtime image. Entry point: proverinterface.webserver.IPLWebServer
# =============================================================================

# ----- build stage -----------------------------------------------------------
FROM eclipse-temurin:17-jdk-alpine AS build
WORKDIR /work

# Bring in the source tree and the third-party jars that IntelliJ already
# tracks under kems.export/lib. AspectJ source files (.aj) live alongside
# the .java files but are intentionally excluded — javac would not know how
# to compile them and they are not required by the runtime entry point.
COPY kems.prover/src                    ./src
COPY kems.export/lib/ext                ./libs-ext
COPY kems.export/lib/generated          ./libs-generated

# jdom2 is used by util.XMLViewer and main.tableau.RulesUsage. It is not
# bundled in the repo (IntelliJ pulls it from its Maven cache), so fetch
# it from Maven Central here for a self-contained build.
RUN mkdir -p /work/libs-extra && \
    wget -q https://repo1.maven.org/maven2/org/jdom/jdom2/2.0.6/jdom2-2.0.6.jar \
         -O /work/libs-extra/jdom2-2.0.6.jar

# Compile every .java file under src/. The two known generated parsers /
# legacy aspects that the IntelliJ classpath excludes are skipped via
# find's -not patterns so the build stays consistent with the IDE setup.
RUN mkdir -p /work/classes && \
    find ./src -name "*.java" \
        -not -name "*Aspect.java" \
        -not -name "ProofTreeSize.java" \
        -not -name "MemoryUsageTracker.java" \
        -not -name "ProverThreadAspect.java" \
        -not -name "Complexity.java" \
        > sources.txt && \
    CP="libs-ext/*:libs-generated/*:libs-extra/*" && \
    javac -encoding ISO-8859-1 --release 17 -d /work/classes -cp "$CP" \
          -Xlint:none -nowarn -proc:none @sources.txt

# Copy classpath resources (e.g. util/symbols.properties bundles) alongside
# the .class files: javac only compiles, never copies arbitrary resources.
RUN (cd src && find . -type f \( -name "*.properties" -o -name "*.xml" -o -name "*.dtd" \) -print0 | \
     xargs -0 -I '{}' sh -c 'mkdir -p "/work/classes/$(dirname "{}")" && cp "{}" "/work/classes/{}"')

# ----- runtime stage ---------------------------------------------------------
FROM eclipse-temurin:17-jre-alpine
WORKDIR /app

# Only the compiled classes plus jars travel to the runtime image, keeping
# the final image small. The shell stays Alpine for low overhead.
COPY --from=build /work/classes        /app/classes
COPY --from=build /work/libs-ext       /app/libs-ext
COPY --from=build /work/libs-generated /app/libs-generated
COPY --from=build /work/libs-extra     /app/libs-extra

# Default port (Fly.io / Render / Heroku override via $PORT).
ENV PORT=8080
EXPOSE 8080

# JVM tuned for a 256–512 MB container. -XX:+ExitOnOutOfMemoryError ensures
# the platform restarts us cleanly instead of leaving a stuck JVM.
ENV JAVA_OPTS="-XX:MaxRAMPercentage=75 -XX:+ExitOnOutOfMemoryError"

ENTRYPOINT ["sh", "-c", "exec java $JAVA_OPTS -cp /app/classes:/app/libs-ext/*:/app/libs-generated/*:/app/libs-extra/* proverinterface.webserver.IPLWebServer"]
