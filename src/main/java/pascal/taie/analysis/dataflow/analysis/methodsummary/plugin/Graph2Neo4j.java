package pascal.taie.analysis.dataflow.analysis.methodsummary.plugin;

import com.opencsv.CSVWriter;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.language.classes.JMethod;

import java.io.File;
import java.io.FileWriter;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

public class Graph2Neo4j implements Plugin {

    private static final Logger logger = LogManager.getLogger(Graph2Neo4j.class);

    private CSCallGraph csCallGraph;

    private String db_path;

    private Set<JMethod> visited;

    public Graph2Neo4j(CSCallGraph csCallGraph, String db_path) {
        super();
        this.csCallGraph = csCallGraph;
        this.db_path = db_path;
        visited = new HashSet<>();
    }

    @Override
    public void onFinish() {
        String node_path = db_path + "/import/nodes.csv";
        String relationship_path = db_path + "/import/edges.csv";
        try {
            CSVWriter nodeWriter = new CSVWriter(new FileWriter(node_path, false));
            CSVWriter edgeWriter = new CSVWriter(new FileWriter(relationship_path, false));
            String[] nodeHeader = {"signature:ID", "name", "isSource", "isSink", "className", "tc", ":LABEL"};
            nodeWriter.writeNext(nodeHeader);
            String[] edgeHeader = {":START_ID", ":END_ID", ":TYPE" ,"PP"};
            edgeWriter.writeNext(edgeHeader);

            Stream<Edge<CSCallSite, CSMethod>> edges = this.csCallGraph.edges();
            graph2CSV(nodeWriter, edgeWriter, edges);

            String command = "neo4j-admin database import full --nodes=import/nodes.csv --relationships=import/edges.csv --overwrite-destination neo4j";
//            logger.info("[+] use {} to load graph to neo4j", command);
            ProcessBuilder process = new ProcessBuilder("cmd", "/c", command);
            process.directory(new File(db_path + "bin"));
            process.start();

            nodeWriter.close();
            edgeWriter.close();
        } catch (Exception e) {
            logger.info(e);
        }
    }

    private void graph2CSV(CSVWriter nodeWriter, CSVWriter edgeWriter, Stream<Edge<CSCallSite, CSMethod>> edges) {
        edges.forEach(edge -> {
            JMethod callee = edge.getCallee().getMethod();
            JMethod caller = edge.getCallSite().getCallSite().getContainer();
            node2CSV(nodeWriter, callee);
            node2CSV(nodeWriter, caller);
            edge2CSV(edgeWriter, caller.getSignature(), callee.getSignature(), edge.getCSIntContr());
        });
    }

    private void node2CSV(CSVWriter nodeWriter, JMethod node) {
        if (visited.add(node)) {
            String[] line = {
                    node.getSignature(),
                    node.getName(),
                    String.valueOf(node.isSource()),
                    String.valueOf(node.isSink()),
                    node.getDeclaringClass().getName(),
                    Arrays.toString(node.getSink()),
                    "Method"
            };
            nodeWriter.writeNext(line);
        }
    }

    private void edge2CSV(CSVWriter edgeWriter, String caller, String callee, List<Integer> csIntContr) {
        String line = String.format("%s#%s#%s#%s",
                caller,
                callee,
                "CALL",
                csIntContr.toString());
        edgeWriter.writeNext(line.split("#"));
    }

}
