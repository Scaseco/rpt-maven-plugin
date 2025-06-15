package org.aksw.maven.plugin.qlever;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.time.Duration;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;
import java.util.function.LongSupplier;

import org.aksw.commons.io.util.FileUtils;
import org.aksw.commons.io.util.FileUtils.OverwritePolicy;
import org.aksw.jenax.dataaccess.sparql.creator.FileSet;
import org.aksw.jenax.dataaccess.sparql.creator.RDFDatabase;
import org.aksw.jenax.engine.qlever.RdfDatabaseBuilderQlever;
import org.apache.commons.compress.archivers.tar.TarArchiveEntry;
import org.apache.commons.compress.archivers.tar.TarArchiveOutputStream;
import org.apache.commons.compress.compressors.gzip.GzipCompressorOutputStream;
import org.apache.jena.dboe.base.file.Location;
import org.apache.jena.graph.Node;
import org.apache.jena.graph.NodeFactory;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.riot.RDFDataMgr;
import org.apache.jena.riot.RDFFormat;
import org.apache.jena.sparql.core.DatasetGraph;
import org.apache.jena.sparql.core.Quad;
import org.apache.jena.sparql.modify.request.UpdateLoad;
import org.apache.jena.tdb2.TDB2Factory;
import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.plugin.logging.Log;
import org.apache.maven.plugins.annotations.Component;
import org.apache.maven.plugins.annotations.LifecyclePhase;
import org.apache.maven.plugins.annotations.Mojo;
import org.apache.maven.plugins.annotations.Parameter;
import org.apache.maven.project.MavenProject;
import org.apache.maven.project.MavenProjectHelper;
import org.eclipse.aether.RepositorySystem;
import org.eclipse.aether.RepositorySystemSession;
import org.eclipse.aether.artifact.Artifact;
import org.eclipse.aether.collection.CollectRequest;
import org.eclipse.aether.graph.Dependency;
import org.eclipse.aether.graph.DependencyFilter;
import org.eclipse.aether.repository.RemoteRepository;
import org.eclipse.aether.resolution.ArtifactResult;
import org.eclipse.aether.resolution.DependencyRequest;
import org.eclipse.aether.resolution.DependencyResult;
import org.eclipse.aether.util.artifact.JavaScopes;
import org.eclipse.aether.util.filter.DependencyFilterUtils;

import com.google.common.io.CountingInputStream;

@Mojo(name = "load", defaultPhase = LifecyclePhase.PACKAGE)
public class QleverMojoLoad extends AbstractMojo {

    /** The repository system (Aether) which does most of the management. */
    @Component
    private RepositorySystem repoSystem;

    /** The current repository/network configuration of Maven. */
    @Parameter(defaultValue = "${repositorySystemSession}", readonly = true)
    private RepositorySystemSession repoSession;

    /** The project's remote repositories to use for the resolution of project dependencies. */
    @Parameter(defaultValue = "${project.remoteProjectRepositories}", readonly = true)
    private List<RemoteRepository> projectRepos;

    /** The Maven project */
    @Parameter(defaultValue = "${project}", readonly = true)
    private MavenProject project;

    @Component
    private MavenProjectHelper mavenProjectHelper;

    @Parameter(property = "qlever.skip", defaultValue = "false")
    protected boolean skip;

    @Parameter(property = "qlever.stxxlMemory")
    private String stxxlMemory;

    /**
     * Comma separated list of dependency type suffixes which to include.
     * A type matches if the string after stripping the suffix is empty or ends with a dot.
     *
     * Examples:
     * "nt" matches the suffix "nt" because "" is the empty string.
     * "rml.ttl" matches the suffix "ttl" because "rml." ends with a dot.
     * "hint" does NOT match "nt" because "hi" is neither the empty string nor does it end with a dot.
     *
     */
    // TODO Generate content-type+encoding combinations from registries
    // content types: nt, ttl, nq, trig, owl (could be obtained from Jena registry)
    // compression encodings: gz, bz2 (could be obtained from commons compress)

    @Parameter(defaultValue = "nt,ttl,nq,trig,owl,nt.gz,ttl.gz,nq.gz,trig.gz,owl.gz,nt.bz2,ttl.bz2,nq.bz2,trig.bz2,owl.bz2")
    private String includeTypes;

    @Parameter(defaultValue = "${project.build.directory}/qlever")
    private File outputFolder;

    /** Output file (the folder as an archive) */
    @Parameter(defaultValue = "${project.build.directory}/qlever.tar.gz")
    private File outputFile;

    /**
     * If unspecified or blank then each dependency is loaded into its own graph by default.
     * If a target graph is given then all dependencies are merged into this graph.
     */
    @Parameter(property = "qlever.targetGraph", defaultValue = "")
    private String targetGraph;

    /** Output file (the folder as an archive) */
//    @Parameter(defaultValue = "${project.build.directory}/tdb2.load.ttl")
//    private File loadStateFile;

    /**
     * Artifacts can be patterns for matching direct dependencies.
     *
     * TODO DRAFT:
     * {@code *} Is a placeholder for matching all characters except for {@code :}.
     * E.g. my.group:*:*:ttl (any artifact, any version, ttl)
     * {@code **} Matches any character including {@code :}.
     *
     * TODO How to omit matches from e.g. the default mapping?
     * Default mapping maps each dataset to a graph with name of the artifact.
     *
     * To map everything into the default graph use
     * <graphMap>
     *   <graph>DEFAULT</graph>
     *   <patterns>
     *     <pattern>*:*:*:*:*</pattern>
     *   <patterns>
     *   <unpool>true</unpool>
     * </graphMap>
     *
     * Use the goal qlever:graphmap to inspect the graph mapping without performing a load.
     */
//    public static class GraphArtifactMapping {
//        protected String graph;
//        protected List<String> artifacts = new ArrayList<>();
//
//        public String getGraph() { return graph; }
//        public void setGraph(String graph) { this.graph = graph; }
//
//        public List<String> getArtifacts() {
//            return artifacts;
//        }
//    }

    // File-based mapping requires a project folder and is thus not self-contained to a pom
    // in contrast to artifact-based mappings.
    public static class FileToGraphMapping {
        protected File file;
        protected String graph;

        public File getFile() { return file; }
        public void setFile(File file) { this.file = file; }
        public String getGraph() { return graph; }
        public void setGraph(String graph) { this.graph = graph; }
    }

    /** Mapping of extra files to graphs. */
    @Parameter
    private List<FileToGraphMapping> files = new ArrayList<>();

    /** Whether to create an archive from the database folder */
    @Parameter(defaultValue = "true")
    private boolean createArchive;

    /** Whether to attach the created archive (only applicable if an archive was created) */
    @Parameter(defaultValue = "true")
    private boolean attachArchive;

    /** Output format */
//    @Parameter
//    private String outputFormat;

    @Override
    public void execute() throws MojoExecutionException {
        if (!skip) {
            JenaMojoHelper.execJenaBasedMojo(this::executeActual);
        }
    }

    public void executeActual() throws Exception {
        Log logger = getLog();

        // Test creation first before resolving dependencies
        Path outputPath = outputFolder.toPath();
        Location location = Location.create(outputPath);
        {
            DatasetGraph dg = TDB2Factory.connectDataset(location).asDatasetGraph();
            dg.close();
        }

        DependencyFilter classpathFlter = DependencyFilterUtils.classpathFilter(JavaScopes.COMPILE);
        CollectRequest collectRequest = new CollectRequest();
        for (org.apache.maven.model.Dependency dep : project.getDependencies()) {
            collectRequest.addDependency(new Dependency(new org.eclipse.aether.artifact.DefaultArtifact(
                    dep.getGroupId(), dep.getArtifactId(), dep.getClassifier(),
                    dep.getType(), dep.getVersion()), JavaScopes.COMPILE));
        }

        collectRequest.setRepositories(project.getRemoteProjectRepositories());
        DependencyRequest dependencyRequest = new DependencyRequest(collectRequest, classpathFlter);

        Set<String> includeTypeSet = new HashSet<>(Arrays.asList(includeTypes.split(",")));

        DependencyResult dependencyResult = repoSystem.resolveDependencies(repoSession, dependencyRequest);

        List<UpdateLoad> workloads = new ArrayList<>();
        for (ArtifactResult artifactResult : dependencyResult.getArtifactResults()) {
            Artifact artifact = artifactResult.getArtifact();
            String extension = artifact.getExtension();

            boolean accept = false;
            for (String suffix : includeTypeSet) {
                if (extension.endsWith(suffix)) {
                    int l = extension.length();
                    String tmp = extension.substring(0, l - suffix.length());
                    accept = tmp.isEmpty() || tmp.endsWith(".");
                }
            }

            if (!accept) {
                logger.debug("Ignoring " + artifact);
                continue;
            }

            File artifactFile = artifactResult.getArtifact().getFile();
            String artifactPath = artifactFile.getAbsolutePath();

            Node graphNode = calcTargetGraphNode(artifact);
            logger.info("Selecting Qlever workload: " + artifactPath + " -> " + graphNode);

            UpdateLoad update = new UpdateLoad(artifactPath, graphNode);
            workloads.add(update);
        }

        for (FileToGraphMapping mapping : files) {
            String graphName = mapping.getGraph();
            File file = mapping.getFile();
            String pathStr = file.getAbsolutePath();

            Node graphNode = graphName == null || graphName.isBlank()
                    ? null
                    : NodeFactory.createURI(graphName);

            UpdateLoad update = new UpdateLoad(pathStr, graphNode);

            String graphNodeLabel = getGraphLabel(graphNode);
            logger.info("Selecting Qlever workload: " + pathStr + " -> " + graphNodeLabel);
            workloads.add(update);
        }

        // XXX This is a simple change detection procedure that needs to evolve in the future.
        // It does not handle the case where multiple files are mapped to the same graph.
        // In general, we need to create a metadata file, tdb instance or graph to do the book-keeping

        String loadStateIri = "urn:load-state";
        LoadState loadState;
        Path loadStatePath = outputPath.resolveSibling("qlever.loadstate.ttl");
        if (Files.exists(loadStatePath)) {
            Model loadStateModel = RDFDataMgr.loadModel(loadStatePath.toAbsolutePath().toString());
            loadState = loadStateModel.createResource(loadStateIri).as(LoadState.class);
        } else {
            loadState = ModelFactory.createDefaultModel().createResource(loadStateIri).as(LoadState.class);
        }

        boolean[] change = {false};
        // Dataset dataset = TDB2Factory.connectDataset(location);

        String indexName = project.getArtifactId() + "-" + project.getVersion();
        RdfDatabaseBuilderQlever<?> dbLoader = new RdfDatabaseBuilderQlever<>()
                .setStxxlMemory(stxxlMemory)
                .setOutputFolder(outputPath)
                .setIndexName(indexName);

        FileSet qleverFileSet;
        try {
            // DatasetGraph dg = dataset.asDatasetGraph();
            for (UpdateLoad update : workloads) {
                String source = update.getSource();
                Node destNode = update.getDest();

                String destNodeLabel = getGraphLabel(destNode);
                boolean isAlreadyLoaded = loadState.getFileStates().containsKey(source);

                if (isAlreadyLoaded) {
                    logger.info("Skipping Qlever workload (already loaded): " + source + " -> " + destNodeLabel);
                } else {
                    logger.info("Batching Qlever workload: " + source + " -> " + destNodeLabel);
                    FileState fileState = loadState.getModel().createResource().as(FileState.class);
                    if (destNode != null) {
                        fileState.getGraphs().add(destNode);
                    }
                    loadState.getFileStates().put (source, fileState);

                    dbLoader.addPath(source, destNode);
                }
            }

            RDFDatabase database = dbLoader.build();
            qleverFileSet = database.getFileSet();

            try {
                FileUtils.safeCreate(loadStatePath, OverwritePolicy.OVERWRITE, out -> {
                    RDFDataMgr.write(out, loadState.getModel(), RDFFormat.TURTLE_PRETTY);
                });
            } catch (Exception e) {
                throw new RuntimeException(e);
            }

        } finally {
            // dataset.close();
            // StoreConnection.release(location);
            // Not sure whether there is a clean way to remove the lock files
//            Files.deleteIfExists(outputPath.resolve("tdb.lock"));
//            Files.deleteIfExists(outputPath.resolve("Data-0001/tdb.lock"));
            // ProcessFileLock lock = DatabaseConnection.lockForLocation(TDB2Factory.location(dataset));
//            Path path = lock.getPath();
//            logger.info("TDB2 file lock is: " + path);
//
//            ProcessFileLock.release(lock);
//            Files.delete(path);
        }

        if (createArchive) {
            Path outputFolderPath = outputFolder.toPath().toAbsolutePath();

            Path tgtFile = outputFile.toPath().toAbsolutePath();
            Path tgtTmpFile = tgtFile.resolveSibling("." + tgtFile.getFileName().toString());

            if (Files.exists(tgtFile) && !change[0]) {
                logger.info("No changes detected. Archive already exists: " + tgtFile);
            } else {
                Path relPath = project.getFile().toPath().getParent();
                logger.info("Writing temp archive: " + tgtTmpFile);
                logger.info("Shown paths are relative to: " + relPath);

                Map<String, Path> fileSet = createQleverFileSet(qleverFileSet);
                packageTdb2(logger::info, tgtTmpFile, fileSet, relPath);
                atomicMoveOrCopy(logger::warn, tgtTmpFile, tgtFile);
                logger.info("Created archive: " + tgtFile);
            }

            if (attachArchive) {
                mavenProjectHelper.attachArtifact(project, "qlever.tar.gz", outputFile);
            }
        }
    }

    protected Node calcTargetGraphNode(Artifact artifact) {
        Node result;
        if (targetGraph == null || targetGraph.isBlank()) {
            result = NodeFactory.createURI("urn:mvn:" + toString(artifact));
        } else {
            if (targetGraph.equalsIgnoreCase("default")) {
                result = null;
            } else {
                Node node = NodeFactory.createURI(targetGraph);
                result = Quad.isDefaultGraph(node) ? null : node;
            }
        }
        return result;
    }

    public static String getGraphLabel(Node graphNode) {
        String result = graphNode == null ? "(default graph)" : graphNode.toString();
        return result;
    }

    public static void atomicMoveOrCopy(Consumer<String> warnCallback, Path source, Path target) throws IOException {
        try {
            Files.move(source, target, StandardCopyOption.ATOMIC_MOVE, StandardCopyOption.REPLACE_EXISTING);
        } catch (IOException e) {
            warnCallback.accept(String.format("Atomic move from %s to %s failed, falling back to copy", source, target));
            Files.move(source, target, StandardCopyOption.REPLACE_EXISTING);
        }
    }

    public static Map<String, Path> createQleverFileSet(FileSet folderToPackage) throws IOException {
        Map<String, Path> result = new LinkedHashMap<>();
        for (Path path : folderToPackage.getPaths()) {
            result.put(path.getFileName().toString(), path);
        }
        return result;
    }

    public static long totalSize(Iterator<Path> files) throws IOException {
        long result = 0;
        while (files.hasNext()) {
            Path path = files.next();
            result += Files.size(path);
        }
        return result;
    }

    private static class Tracker {
        int    maxDataPoints = 10;
        Deque<Entry<Long, Long>> timeAndTotalProgress = new ArrayDeque<>(maxDataPoints);


        long   totalSize = -1;
        int    fileCount = -1;
        long   currentFileStartProgress = 0; // Progress before the current file
        LongSupplier currentFileProgress;
        // totalProgress = currentFileStartProgress + currentFileProgress.getAsLong()

        String currentFileName = null;
        int    currentFileIdx = 0;
        long   currentFileSize = -1;
        // long   currentFileProgress = -1;
    }

    public static void packageTdb2(Consumer<String> fileCallback, Path fileToWrite, Map<String, Path> fileSet, Path basePath) throws IOException {
        try (OutputStream fOut = Files.newOutputStream(fileToWrite);
            BufferedOutputStream buffOut = new BufferedOutputStream(fOut);
            GzipCompressorOutputStream gzOut = new GzipCompressorOutputStream(buffOut);
            TarArchiveOutputStream tOut = new TarArchiveOutputStream(gzOut)) {
            tOut.setLongFileMode(TarArchiveOutputStream.LONGFILE_GNU);
            tOut.setBigNumberMode(TarArchiveOutputStream.BIGNUMBER_POSIX);

            Tracker tracker = new Tracker();
            tracker.totalSize = totalSize(fileSet.values().iterator());
            tracker.fileCount = fileSet.size();

            // long startTime = System.currentTimeMillis();
            Runnable monitorProgress = () -> {
                long elapsedTime = System.currentTimeMillis();
                long currentFileProgress = tracker.currentFileProgress.getAsLong();
                long totalProgress = tracker.currentFileStartProgress + currentFileProgress;

                float fileRatio = tracker.currentFileSize == 0
                    ? 1.0f
                    : currentFileProgress / (float)tracker.currentFileSize;

                float totalRatio = tracker.totalSize == 0
                    ? 1.0f
                    : totalProgress / (float)tracker.totalSize;

                Deque<Entry<Long, Long>> points = tracker.timeAndTotalProgress;
                if (points.size() >= tracker.maxDataPoints) {
                    points.removeFirst();
                }
                Entry<Long, Long> newEntry = Map.entry(elapsedTime, totalProgress);
                points.addLast(newEntry);
                Entry<Long, Long> oldEntry = points.getFirst();

                float relDuration = (newEntry.getKey() - oldEntry.getKey()) * 0.001f; // ms to seconds
                long relAmount = newEntry.getValue() - oldEntry.getValue();
                float throughput = relDuration < 0.001f ? 0f : relAmount / relDuration;

                long remaining = tracker.totalSize - totalProgress;
                long etaInSeconds = throughput < 0.001f ? Long.MAX_VALUE : (long)(remaining / throughput);
                if (etaInSeconds == 0 && remaining > 0) {
                    etaInSeconds = 1;
                }
                String etaStr = etaInSeconds == Long.MAX_VALUE
                        ? "infinite"
                        : toString(Duration.ofSeconds(etaInSeconds));

                String msg = String.format("Adding file %d/%d %s %.2f%% - Total %.2f%% - ETA %s",
                        tracker.currentFileIdx, tracker.fileCount, tracker.currentFileName,
                        fileRatio * 100.0f, totalRatio * 100.0f, etaStr);

                fileCallback.accept(msg);
            };

            for (Entry<String, Path> e : fileSet.entrySet()) {
                String relPathStr = e.getKey();
                Path file = e.getValue();
                Path displayPath = basePath == null ? file : basePath.relativize(file);

                ++tracker.currentFileIdx;
                tracker.currentFileName = displayPath.toString();
                tracker.currentFileSize = Files.size(file);

                TarArchiveEntry tarEntry = new TarArchiveEntry(file, relPathStr);
                tOut.putArchiveEntry(tarEntry);

                ScheduledExecutorService ses = Executors.newSingleThreadScheduledExecutor();
                try (CountingInputStream cin = new CountingInputStream(Files.newInputStream(file))) {
                    tracker.currentFileProgress = () -> cin.getCount();
                    ScheduledFuture<?> future = ses.scheduleAtFixedRate(monitorProgress, 1, 10, TimeUnit.SECONDS);
                    try {
                        cin.transferTo(tOut);
                    } finally {
                        future.cancel(false);
                    }
                } finally {
                    ses.shutdown();
                    try {
                        if (!ses.awaitTermination(5, TimeUnit.SECONDS)) {
                            throw new RuntimeException("Progress monitor: Failed to stop.");
                        }
                    } catch (InterruptedException e1) {
                        throw new RuntimeException("Progress monitor: Unexpected interruption", e1);
                    }
                }
                monitorProgress.run();
                tracker.currentFileStartProgress += tracker.currentFileProgress.getAsLong();
                tOut.closeArchiveEntry();
            }
            tOut.finish();
        }
    }

    public static String toString(Duration eta) {
        int s = eta.toSecondsPart();
        int m = eta.toMinutesPart();
        int h = eta.toHoursPart();
        long d = eta.toDaysPart();

        StringBuilder b = new StringBuilder();
        if (d != 0) {
            if (!b.isEmpty()) { b.append(" "); }
            b.append(d).append("d");
        }

        if (h != 0) {
            if (!b.isEmpty()) { b.append(" "); }
            b.append(h).append("h");
        }

        if (m != 0) { // d != 0 || h != 0 ||
            if (!b.isEmpty()) { b.append(" "); }
            b.append(m).append("m");
        }

        if (!b.isEmpty()) { b.append(" "); }
        b.append(s).append("s");
        return b.toString();
    }

    protected String toString(Artifact coord) {
        String t = coord.getExtension();
        String c = coord.getClassifier();

        String suffix =
                (t == null || t.isEmpty() ? "" : ":" + t) +
                (c == null || c.isEmpty() ? "" : ":" + c);

        String result = coord.getGroupId() + ":" + coord.getArtifactId() + ":" + coord.getVersion() + suffix;
        return result;
    }

    public Path relativizeAgainstPom(File file) {
        Path pom = project.getFile().toPath().getParent();
        Path result = pom.relativize(file.toPath());
        return result;
    }

    public Path resolveAgainstPom(Path path) {
        Path pom = project.getFile().toPath().getParent();
        Path result = pom.resolve(path);
        return result;
    }
}
