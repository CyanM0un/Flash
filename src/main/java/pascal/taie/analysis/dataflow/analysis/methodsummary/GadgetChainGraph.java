package pascal.taie.analysis.dataflow.analysis.methodsummary;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;

import java.util.*;

public class GadgetChainGraph {

    private Map<String, GadgetChainNode> adjList;

    private static int PATH_MAX_COUNT = World.get().getOptions().getPATH_MAX_COUNT();

    private static int PATH_COLLECT_TIME = World.get().getOptions().getPATH_COLLECT_TIME();

    private static final Logger logger = LogManager.getLogger(GadgetChainGraph.class);

    public GadgetChainGraph() {
        this.adjList = new HashMap<>();
    }


    public boolean addPath(List<String> path) {
        boolean add = false;
        int size = path.size();
        for (int i = 0; i < size; i++) {
            String m = path.get(i);
            if (!adjList.containsKey(m)) {
                add = true;
                adjList.put(m, new GadgetChainNode(m));
            }
            if (i != size - 1) {
                addEdge(m, path.get(i + 1));
            }
        }
        return add;
    }

    private void addEdge(String from, String to) {
        adjList.get(from).addNext(to);
    }

    public Set<List<String>> collectPath(String from) {
        Set<List<String>> paths = new HashSet<>();
        List<String> path = new ArrayList<>();
        Set<String> visited = new HashSet<>();
        long startTime = System.currentTimeMillis();
        dfsCollectPaths(from, visited, path, paths, startTime);
//        long endTime = System.currentTimeMillis();
//        logger.info("collect {} path in {}s", paths.size() , (endTime - startTime) / 1000);
        return paths;
    }

    private void dfsCollectPaths(String current, Set<String> visited, List<String> path, Set<List<String>> paths, long startTime) {
        if (paths.size() >= PATH_MAX_COUNT || path.contains(current) || System.currentTimeMillis() - startTime > PATH_COLLECT_TIME) return;
        visited.add(current);
        path.add(current);

        if (!adjList.containsKey(current)) {
            path.remove(path.size() - 1);
            visited.remove(current);
            return;
        }
        boolean isSink = adjList.get(current).isLeaf();
        if (isSink) {
            paths.add(new ArrayList<>(path));
        } else if (path.size() == StackManger.MAX_LEN) {
            path.remove(path.size() - 1);
            visited.remove(current);
            return;
        }

        for (String neighbor : adjList.get(current).getNexts()) {
            if (!visited.contains(neighbor)) {
                dfsCollectPaths(neighbor, visited, path, paths, startTime);
            }
        }

        path.remove(path.size() - 1);
        visited.remove(current);
    }

    public boolean containsNode(String key) {
        return adjList.containsKey(key);
    }
}
