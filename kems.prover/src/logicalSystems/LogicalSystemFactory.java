/*
 * Created on 03/08/2005
 *
 */
package logicalSystems;

import java.util.HashMap;
import java.util.Map;

import logic.logicalSystem.ILogicalSystem;
import logicalSystems.classicalLogic.ClassicalLogicSystem;
import logicalSystems.classicalLogic.ClassicalRulesStructureBuilder;
import logicalSystems.classicalLogic.ClassicalSignatureFactory;
import logicalSystems.ipl.IPLLogicSystem;
import logicalSystems.ipl.IPLRulesStructureBuilder;
import logicalSystems.ipl.IPLSignatureFactory;

/**
 * A factory of logical system objects. It is a singleton.
 * 
 * @author Adolfo Gustavo Serra Seca Neto
 * 
 *  
 */
public class LogicalSystemFactory {
    /** constants for logical systems */
    public static final Object CLASSICAL_LOGIC = new Object();
    public static final Object IPL_LOGIC = new Object();

    private static LogicalSystemFactory __logicalSystemFactory;

    private ClassicalSignatureFactory classicalSignatureFactory;
    private IPLSignatureFactory iplSignatureFactory;

    private Map<Object,ILogicalSystem> logicalSystemsMap;

    private LogicalSystemFactory() {
        logicalSystemsMap = new HashMap<Object, ILogicalSystem>();
    }

    public static LogicalSystemFactory getInstance() {
        if (__logicalSystemFactory == null) {
            __logicalSystemFactory = new LogicalSystemFactory();
        }

        return __logicalSystemFactory;
    }

    /**
     * creates
     * 
     * @param id
     * @return a logical system
     */
    public ILogicalSystem getLogicalSystem(Object id) {
        if (id == CLASSICAL_LOGIC) {
            if (logicalSystemsMap.get(CLASSICAL_LOGIC) == null) {
                this.classicalSignatureFactory = ClassicalSignatureFactory
                        .getInstance();
                ILogicalSystem ils = new ClassicalLogicSystem(
                        classicalSignatureFactory.getNormalBXSignature(),
                        new ClassicalRulesStructureBuilder());
                logicalSystemsMap.put(CLASSICAL_LOGIC, ils);
                return ils;
            } else
                return (ILogicalSystem) logicalSystemsMap.get(CLASSICAL_LOGIC);
        } else if (id == IPL_LOGIC) {
            if (logicalSystemsMap.get(IPL_LOGIC) == null) {
                this.iplSignatureFactory = IPLSignatureFactory.getInstance();
                ILogicalSystem ils = new IPLLogicSystem(
                        iplSignatureFactory.getNormalSignature(),
                        new IPLRulesStructureBuilder());
                logicalSystemsMap.put(IPL_LOGIC, ils);
                return ils;
            } else
                return (ILogicalSystem) logicalSystemsMap.get(IPL_LOGIC);
        }

        return null;

    }

}
