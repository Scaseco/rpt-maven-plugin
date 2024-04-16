package org.aksw.maven.plugin.lsq;

import java.io.File;

import org.apache.jena.sys.JenaSystem;
import org.apache.maven.plugin.Mojo;
import org.apache.maven.plugin.testing.MojoRule;
import org.apache.maven.project.MavenProject;
import org.junit.Rule;
import org.junit.Test;

public class TestLsqBenchmarkMojo {

    static { JenaSystem.init(); }

    @Rule
    public MojoRule rule = new MojoRuleNoOp();

    @Test
    public void testMojoGoal() throws Exception {
        File file = new File("src/test/resources/lsq/test-benchmark-01");
        MavenProject project = rule.readMavenProject(file);
        Mojo mojo = rule.lookupConfiguredMojo(project, "benchmark");
        mojo.execute();
    }
}