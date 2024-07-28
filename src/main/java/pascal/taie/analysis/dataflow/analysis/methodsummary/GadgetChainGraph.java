package pascal.taie.analysis.dataflow.analysis.methodsummary;

import java.util.*;

public class GadgetChainGraph {

    private Map<String, Set<String>> adjList;

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
                adjList.put(m, new HashSet<>());
            }
            if (i != size - 1) {
                addEdge(m, path.get(i + 1));
            }
        }
        return add;
    }

    public void addPaths(Set<List<String>> paths) {
        paths.forEach(path -> addPath(path));
    }

    private void addEdge(String from, String to) {
        adjList.get(from).add(to);
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
        boolean isSink = adjList.get(current).isEmpty();
        if (isSink) {
            paths.add(new ArrayList<>(path));
        } else if (path.size() == StackManger.MAX_LEN) {
            path.remove(path.size() - 1);
            visited.remove(current);
            return;
        }

        for (String neighbor : adjList.get(current)) {
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
            if (i != size - 1 && !adjList.get(node).contains(path.get(i + 1))) return false;
        }
        return true;
    }
}
