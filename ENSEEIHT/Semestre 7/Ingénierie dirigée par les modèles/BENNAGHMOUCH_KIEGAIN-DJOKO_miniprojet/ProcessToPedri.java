import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.xmi.impl.XMIResourceFactoryImpl;

import petrinet.*;
import simplepdl.*;
import simplepdl.SimplepdlFactory;
import simplepdl.SimplepdlPackage;
import simplepdl.WorkDefinition;
import simplepdl.WorkSequence;
import simplepdl.WorkSequenceType;

public class ProcessToPedri {

	public static void main(String[] args) {
		
		// Charger le package SimplePDL afin de l'enregistrer dans le registre d'Eclipse.
		SimplepdlPackage processPackageInstance = SimplepdlPackage.eINSTANCE;
		PetrinetPackage petriPackageInstance = PetrinetPackage.eINSTANCE;
		
		// Enregistrer l'extension ".xmi" comme devant Ãªtre ouverte Ã 
		// l'aide d'un objet "XMIResourceFactoryImpl"
		Resource.Factory.Registry reg = Resource.Factory.Registry.INSTANCE;
		Map<String, Object> m = reg.getExtensionToFactoryMap();
		m.put("xmi", new XMIResourceFactoryImpl());
		
		// CrÃ©er un objet resourceSetImpl qui contiendra une ressource EMF (le modÃ¨le)
		ResourceSet resSet = new ResourceSetImpl();

		// DÃ©finir la ressource (le modÃ¨le)
		URI modelURI1 = URI.createURI("models/process1.xmi");
		Resource processResource = resSet.getResource(modelURI1,true);
		URI modelURI2 = URI.createURI("models/net1.xmi");
		Resource petriResource = resSet.createResource(modelURI2);
		
		// La fabrique pour fabriquer les Ã©lÃ©ments de SimplePDL
	    SimplepdlFactory myProcessFactory = SimplepdlFactory.eINSTANCE;
	    PetrinetFactory myPetriFactory = PetrinetFactory.eINSTANCE;

		// CrÃ©er un Ã©lÃ©ment Process
	    simplepdl.Process process = (simplepdl.Process) processResource.getContents().get(0);
		Net petri = myPetriFactory.createNet();
		petri.setName("PetriNet");
		
		// Ajouter le Process dans le modÃ¨le
		petriResource.getContents().add(petri);
		
		Map <String, Place> name_place= new HashMap<>();
		Map <String, Transition> Wd_transition= new HashMap<>();
		Map <String, Transition> name_transition= new HashMap<>();
		
		for (Object o : process.getProcessElements()) {
			if (o instanceof WorkDefinition) {
				WorkDefinition wd = (WorkDefinition) o;
				Place pl_ready = myPetriFactory.createPlace(); petri.getNetElement().add(pl_ready);
				pl_ready.setName(wd.getName()+"_ready");
				pl_ready.setToken(1);
				
				Place pl_started = myPetriFactory.createPlace(); petri.getNetElement().add(pl_started);
				pl_started.setName(wd.getName()+"_started");
				
				Place pl_running = myPetriFactory.createPlace(); petri.getNetElement().add(pl_running);
				pl_running.setName(wd.getName()+"_running"); name_place.put(pl_running.getName(), pl_running);
				
				Place pl_finished = myPetriFactory.createPlace(); petri.getNetElement().add(pl_finished);
				pl_finished.setName(wd.getName()+"_finished"); name_place.put(pl_finished.getName(), pl_finished);
				
				Transition tr_r2r = myPetriFactory.createTransition(); petri.getNetElement().add(tr_r2r);
				tr_r2r.setName(wd.getName()+"_start");
				Wd_transition.put(wd.getName(), tr_r2r); name_transition.put(tr_r2r.getName(), tr_r2r);
				
				Transition tr_r2f = myPetriFactory.createTransition(); petri.getNetElement().add(tr_r2f);
				tr_r2f.setName(wd.getName()+"_finish"); name_transition.put(tr_r2f.getName(), tr_r2f);
				
				Arc a1 = myPetriFactory.createArc(); petri.getNetElement().add(a1);
				Arc a2 = myPetriFactory.createArc(); petri.getNetElement().add(a2);
				Arc a3 = myPetriFactory.createArc(); petri.getNetElement().add(a3);
				Arc a4 = myPetriFactory.createArc(); petri.getNetElement().add(a4);
				Arc a5 = myPetriFactory.createArc(); petri.getNetElement().add(a5);
				
				pl_ready.getOutArc().add(a1);
				tr_r2r.getInArc().add(a1);
				tr_r2r.getOutArc().add(a2);
				tr_r2r.getOutArc().add(a5);
				pl_started.getInArc().add(a5);
				pl_running.getInArc().add(a2);
				pl_running.getOutArc().add(a3);
				tr_r2f.getInArc().add(a3);
				tr_r2f.getOutArc().add(a4);
				pl_finished.getInArc().add(a4);
				
				arcName(a1);		arcName(a2);		arcName(a3);		arcName(a4);		arcName(a5);
			}
		}

		Map <String, Place> ressource_place= new HashMap<>();
		for (Object o : process.getProcessElements()) {
			if (o instanceof simplepdl.Resource) {
				simplepdl.Resource res = (simplepdl.Resource) o;
				Place res_pl = myPetriFactory.createPlace(); petri.getNetElement().add(res_pl);
				res_pl.setName(res.getName());
				res_pl.setToken(res.getQuantity());
				ressource_place.put(res.getName(), res_pl);
			}
		}
		
		for (Object o : process.getProcessElements()) {
			if (o instanceof WorkDefinition) {
				WorkDefinition wd = (WorkDefinition) o;
				Transition tr = Wd_transition.get(wd.getName());
				for (Allocate use : wd.getAllocate()) {
					Arc a = myPetriFactory.createArc(); petri.getNetElement().add(a);
					a.setWeigth(use.getOccurence());
					tr.getInArc().add(a);
					a.setSource(ressource_place.get(use.getResource().getName()));
					arcName(a);
				}
			}
		}
		
		for (Object o : process.getProcessElements()) {
			if (o instanceof WorkSequence) {
				WorkSequence ws = (WorkSequence) o;
				Arc a = myPetriFactory.createArc(); petri.getNetElement().add(a);
				a.setType(ArcType.READ_ARC);
				String src = (ws.getLinkType() == WorkSequenceType.FINISH_TO_FINISH || ws.getLinkType() == WorkSequenceType.FINISH_TO_START ) ? "_finish" : "_start";
				String dst = (ws.getLinkType() == WorkSequenceType.FINISH_TO_START || ws.getLinkType() == WorkSequenceType.START_TO_START ) ? "_start" : "_finish";
				a.setSource(name_place.get(ws.getPredecessor().getName()+src+"ed"));
				a.setTarget(name_transition.get(ws.getSuccessor().getName()+dst));
				arcName(a);
			}
		}
		
		// Sauver la ressource
	    try {
	    	petriResource.save(Collections.EMPTY_MAP);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public static void arcName(Arc arc) {
		arc.setName("("+arc.getSource().getName()+"->"+arc.getTarget().getName()+")");
	}
}



