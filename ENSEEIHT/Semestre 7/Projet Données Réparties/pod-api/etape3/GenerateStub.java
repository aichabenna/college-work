import java.io.File;
import java.io.FileOutputStream;
import java.lang.reflect.Method;
import java.lang.reflect.Parameter;

public class GenerateStub {

    public static void generateClassStub(Class classe) {
        try {
            // class Name
            String interfaceName = classe.getName();
            // take off _itf
            String className = interfaceName.substring(0, interfaceName.length() - 4);
            String stubClassName = className + "_stub";
            String filename = stubClassName + ".java";
            String file_content = "";

            // file begin
            file_content = file_content + "public class " + stubClassName + " extends SharedObject implements "
                    + interfaceName + ", java.io.Serializable {\n";

            // class constructor
            file_content = file_content + "     public " + stubClassName + "(int id, Object o) {\n";
            file_content = file_content + "         super(id,o);\n";
            file_content = file_content + "     }\n";

            // class methods
            Method[] methods = classe.getDeclaredMethods();
            String method;
            for (Method m : methods) {
                String methodName = m.getName();
                String methodType = m.getReturnType().getTypeName();

                // declaration
                method = "  public " + methodType + " " + methodName + "(";
                // method parameters
                Parameter[] parameters = m.getParameters();
                int nbParameters = parameters.length;
                String methodParameters = "";
                for (Parameter parameter : parameters) {
                    methodParameters = methodParameters + parameter.getType().getName() + " " + parameter.getName();
                    nbParameters--;
                    if (nbParameters != 0) {
                        methodParameters += ", ";
                    }
                }
                method += methodParameters + ") {\n";

                // method instructions
                String obj = "      " + className + " object = (" + className + ") obj;\n";
                String methodApp = "object." + methodName + "(";
                methodParameters = "";
                nbParameters = parameters.length;
                for (Parameter parameter : parameters) {
                    methodParameters = methodParameters + parameter.getName();
                    nbParameters--;
                    if (nbParameters != 0) {
                        methodParameters += ", ";
                    }
                }
                methodParameters += ");\n   }\n\n";
                methodApp += methodParameters;

                if (methodType.equals("void")) { // methodType
                    method += obj + "       " + methodApp;
                } else {
                    method += obj + "       return " + methodApp;
                }
                file_content = file_content + method;
            }

            // file end
            file_content = file_content + "}";

            // create stub file
            File stubFile = new File(filename);
            stubFile.createNewFile();
            FileOutputStream stubOutputStream = new FileOutputStream(stubFile);
            stubOutputStream.write(file_content.getBytes());
            stubOutputStream.close();
        } catch (Exception e) {
            System.out.println("Stub generation failed in the function!");
            e.printStackTrace();
        }
    }

    public static void main(String[] args) {
        try {
            generateClassStub(Class.forName(args[0]));
        } catch (Exception e) {
            System.out.println("Stub generation failed in the main!");
            e.printStackTrace();
        }
    }
}