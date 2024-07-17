package pascal.taie.analysis.dataflow.analysis.methodsummary.Utils;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.analysis.dataflow.analysis.ContrAlloc;
import pascal.taie.analysis.dataflow.analysis.methodsummary.Contr;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.Strings;

import java.util.ArrayList;
import java.util.List;

public class ContrUtil {

    public static final int iTHIS = -1;

    public static final int iPOLLUTED = -2;

    public static final int iNOT_POLLUTED = -3;

    public static final String sTHIS = "this";

    public static final String sPOLLUTED = "polluted";

    public static final String sNOT_POLLUTED = "null";

    public static final String sParam = "param";

    private static final Logger logger = LogManager.getLogger(ContrUtil.class);

    public static String int2String(int i) {
        if (i >= 0) return sParam + "-" + i;
        else if (i == iTHIS) return sTHIS;
        else if (i == iPOLLUTED) return sPOLLUTED;
        else return sNOT_POLLUTED;
    }

    public static int string2Int(String s) {
        try {
            if (s == null) return iNOT_POLLUTED;
            else if (s.contains(sPOLLUTED)) return iPOLLUTED;
            else if (s.contains(sTHIS)) return iTHIS;
            else if (s.contains(sParam)) return Strings.extractParamIndex(s);
        } catch (Exception e) {
            logger.info("[-] error parsing {}", s);
        }
        return iNOT_POLLUTED;
    }

    public static List<Integer> string2Int(List<String> values) {
        List<Integer> ret = new ArrayList<>();
        values.forEach(value -> ret.add(string2Int(value)));
        return ret;
    }

    public static boolean needUpdateInMerge(String oldV, String newV) {
        if (oldV == null) return !newV.equals(sNOT_POLLUTED);
        else return string2Int(oldV) == iNOT_POLLUTED && string2Int(newV) != iNOT_POLLUTED;
    }

    public static boolean needUpdateInConcat(String left, String right) {
        return isControllable(left) != isControllable(right);
    }

    public static boolean isControllable(Contr contr) {
        return contr != null && isControllable(contr.getValue());
    }

    public static boolean isControllable(String value) {
        return string2Int(value) >= iPOLLUTED;
    }

    public static boolean isControllableParam(Contr contr) {
        return isControllableParam(contr.getValue());
    }

    public static boolean isControllableParam(String value) {
        return string2Int(value) > iTHIS;
    }

    public static boolean isCallSite(String value) {
        return string2Int(value) >= iTHIS;
    }

    public static String convert2Reg(String v) {
        if (v.contains("+")) {
            StringBuilder ret = new StringBuilder();
            String[] parts = v.split("\\+");
            for (String p : parts) {
                if (isControllable(p) && !ret.toString().endsWith(".*")) {
                    ret.append(".*");
                } else {
                    ret.append(p);
                }
            }
            return ret.toString();
        } else if (isControllable(v)) {
            return ".*";
        } else if (!v.equals(sNOT_POLLUTED)) {
            return v;
        } else {
            return "";
        }
    }

    public static CSObj getObj(Pointer p, String value, HeapModel heapModel, Context context, CSManager csManager) {
        ContrAlloc alloc = new ContrAlloc(p, value);
        Obj obj = heapModel.getMockObj(Descriptor.CONTR_DESC, alloc, p.getType());
        return csManager.getCSObj(context, obj);
    }

    public static boolean isSerializableType(Type type) {
        if (type instanceof ClassType ct) {
            return ct.getJClass().isSerializable();
        } else if (type instanceof ArrayType at) {
            if (at.elementType() instanceof ClassType et) return et.getJClass().isSerializable();
            else return isSerializableType(at.elementType());
        } else if (type instanceof PrimitiveType) {
            return true;
        } else {
            return false;
        }
    }
}
