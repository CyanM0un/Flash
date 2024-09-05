package pascal.taie.analysis.dataflow.analysis.methodsummary;

import java.util.*;

public class GadgetChainGraph {

    private Map<String, GadgetChainNode> adjList;

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
        dfsCollectPaths(from, visited, path, paths);
        return paths;
    }

    private void dfsCollectPaths(String current, Set<String> visited, List<String> path, Set<List<String>> paths) {
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
                dfsCollectPaths(neighbor, visited, path, paths);
            }
        }

        path.remove(path.size() - 1);
        visited.remove(current);
    }

    public boolean containsPath(List<String> path) {
        int size = path.size();
        for (int i = 0; i < size; i++) {
            String node = path.get(i);
            if (!adjList.containsKey(node)) return false;
            if (i != size - 1 && !adjList.get(node).containsNext(path.get(i + 1))) return false;
        }
        return true;
    }

    public void updateTC(String key, List<Integer> tc, String sink) {
        adjList.get(key).updateTC(sink, tc);
    }

    public boolean containsTC(String key) {
        return adjList.containsKey(key) && adjList.get(key).containsTC();
    }

    public List<Integer> getTCList(List<String> toSinkGC) {
        String sink = toSinkGC.get(toSinkGC.size() - 1);
        return getTCList(toSinkGC.get(0), sink);
    }

    public List<Integer> getTCList(String caller, String sink) {
        return adjList.get(caller).getTC(sink);
    }
}
