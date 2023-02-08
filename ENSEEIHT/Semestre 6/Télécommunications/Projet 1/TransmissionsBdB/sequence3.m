%% Etude de l'impact du bruit, filtrage adapte, taux d'erreur binaire, 
%% efficacite en puissance (Sequence 3)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Fe=24000; % Frequence d'echantillonnage
Te=1/Fe; % Periode
Rb=3000; % Debit Bits/s
Tb=1/Rb; % Periode binaire
n=10000; %% Nombre de bits emis
M=2; % nombre de points dans la constellation 
Rs=Rb/log2(M); % Debit Symbole : baud
Ts=1/Rs; % Periode symbole
Ns=Ts/Te; % Nombre de periodes d'echantillonnage par periode symbole

%% -------------------------------------------------------------
%% -----------------Chaine de référence-------------------------
%% -------------------------------------------------------------

t_axis = [1:n/log2(M)*Ns]*Te; % axe temporel
h = ones(1,Ns); % RI du filtre de mise en forme
hr=fliplr(h);
n0=length(hr); % prendre la décision à n0*Te+m*Ts pour estimer am emis a mTs

%% Generation du signal
bits=randi([0,1], 1, n);% generation des bits

%% Mapping
symboles = 2*bits-1; % generation des symboles

%% Suréchantillonnage
peigne = kron(symboles, [1 zeros(1,Ns-1)]); % peigne de Dirac

%% Filtrage de mise en forme
x = filter(h, 1, peigne); % Filtrage de mise en forme

%% Filtrage de réception
z = filter(hr, 1, x);

%% Diagramme de l'oeil
figure('Name',"Diagramme de l'oeil de la chaine de référence sans bruit");
plot(reshape(z, Ns, length(z)/(Ns)));
title("Diagramme de l'oeil de la chaine de référence sans bruit");

%% Echantillonnage 
zm=z(n0:Ns:end);

%% Démapping + TEB 
error=sum((zm>=0)~=bits);
TEB=error/n;

if TEB == 0 
    disp('Chaine de référence sans bruit vérifie bien que TEB est nul');
end
%% %%%%%%%%%%%%%%%%%%%% Avec Bruit %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

EbN0dB=[0:8];
EbN0=10.^(EbN0dB./10);
BER=zeros(1,length(EbN0));
figure('Name', "Chaine de référence: Diagrame de l'oeil en fonction de EbN0dB");
for k=0:(length(EbN0)-1)
    %% Ajout du bruit
    var_bruit(k+1)=mean(abs(x).^2)*Ns./(2*log2(M).*EbN0(k+1));
    r=x+sqrt(var_bruit(k+1))*randn(1,length(x)); % canal AWGN
    
    %% Filtrage de réception
    z = filter(hr, 1, r);

    %% Diagramme de l'oeil
    subplot(3,3,k+1);
    plot(reshape(z, Ns, length(z)/(Ns)));
    title('EbN0dB = ' , num2str(k));

    %% Echantillonnage 
    zm=z(n0:Ns:end);
    
    %% Démapping + TEB 
    erreur(k+1)=sum((zm>=0)~=bits);
    BER(k+1)=erreur(k+1)/n;
    %disp(['TEB = ', num2str(BER(k+1)), ' pour EbN0dB = ', num2str(k)]);
end

figure;
semilogy(EbN0dB,BER,'p--','LineWidth',3);
xlabel('E_b/N_0 (en dB)');
ylabel('TEB');
title('TEB simulé en fonction de EBN0dB (Chaine de référence)');
grid;

figure;
semilogy(EbN0dB,BER,'p--','LineWidth',3);
hold on;
semilogy(EbN0dB,qfunc(sqrt(2*EbN0)),'LineWidth',3);
legend('TEB Simulé', 'TEB Théorique');
xlabel('E_b/N_0 (en dB)');
title('Comparaison des TEB (Chaine de référence)');
grid;

disp('---------------------------');

%% -------------------------------------------------------------
%% ---------------------Première chaine-------------------------
%% -------------------------------------------------------------

%% ----------------------- Sans Bruit --------------------------
%% Generation du signal
bits=randi([0,1], 1, n);% generation des bits

%% Mapping
symboles = 2*bits-1; % generation des symboles

%% Suréchantillonnage
peigne = kron(symboles, [1 zeros(1,Ns-1)]); % peigne de Dirac

%% Filtrage de mise en forme
h = ones(1,Ns);
x = filter(h, 1, peigne); % Filtrage de mise en forme

%% Filtrage de réception
hr = [ones(1,Ns/2) zeros(1,Ns/2)];
n0=length(hr); % prendre la décision à n0*Te+m*Ts pour estimer am emis a mTs
z = filter(hr, 1, x);

%% Diagramme de l'oeil
figure('Name',"Diagramme de l'oeil de la chaine 1 sans bruit");
plot(reshape(z, Ns, length(z)/(Ns)));
title("Diagramme de l'oeil de la chaine 1 sans bruit");

%% Echantillonnage 
zm=z(n0:Ns:end);

%% Démapping + TEB 
error=sum((zm>=0)~=bits);
TEB1=error/n;

if TEB1 == 0 
    disp('Chaine 1 sans bruit vérifie bien que TEB est nul');
end

%% ----------------------- Avec Bruit --------------------------

EbN0dB=[0:8];
EbN0=10.^(EbN0dB./10);
BER1=zeros(1,length(EbN0));
figure('Name', "Chaine 1: Diagrame de l'oeil en fonction de EbN0dB");
for k=0:(length(EbN0)-1)
    %% Ajout du bruit
    var_bruit(k+1)=mean(abs(x).^2)*Ns./(2*log2(M).*EbN0(k+1));
    r=x+sqrt(var_bruit(k+1))*randn(1,length(x)); % canal AWGN
    
    %% Filtrage de réception
    z = filter(hr, 1, r);

    %% Diagramme de l'oeil
    subplot(3,3,k+1);
    plot(reshape(z, Ns, length(z)/(Ns)));
    title('EbN0dB = ' , num2str(k));

    %% Echantillonnage 
    zm=z(n0:Ns:end);
    
    %% Démapping + TEB 
    erreur(k+1)=sum((zm>=0)~=bits);
    BER1(k+1)=erreur(k+1)/n;
    %disp(['TEB = ', num2str(BER1(k+1)), ' pour EbN0dB = ', num2str(k)]);
end

%% TEB simulé en fct de EBN0dB
figure;
semilogy(EbN0dB,BER1,'p--','LineWidth',3);
xlabel('E_b/N_0 (en dB)');
ylabel('TEB');
title('TEB simulé en fonction de EBN0dB (Chaine 1)');
grid;

%% Comparaison TEB avec TEB théorique
figure;
semilogy(EbN0dB,BER1,'p--','LineWidth',3);
hold on;
semilogy(EbN0dB, qfunc(sqrt(10.^(EbN0dB/10))));
title('Comparaison TEB en fonction du EbN0 en dB avec TEB théorique');
xlabel('E_b/N_0 (en dB)');
ylabel('TEB');
legend('TEB Simulé', 'TEB Théorique');
hold off;

%% Comparaison TEB avec TEB de la chaine de référence
figure;
semilogy(EbN0dB, BER1);
hold on;
semilogy(EbN0dB, BER);
title('Comparaison TEB en fonction du EbN0 en dB avec chaine de référence');
legend('TEB: Chaine 1','TEB Chaine référence');
xlabel('EbN0dB');
ylabel('TEB');
hold off;


disp('---------------------------');

%% -------------------------------------------------------------
%% ---------------------Deuxième chaine-------------------------
%% -------------------------------------------------------------
M=4;
Rs=Rb/log2(M); % Debit Symbole : baud
Ts=1/Rs; % Periode symbole
Ns=Ts/Te; % Nombre de periodes d'echantillonnage par periode symbole

%% ----------------------- Sans Bruit --------------------------
%% Generation du signal
bits=randi([0,1], 1, n);% generation des bits

%% Mapping
symboles = (2 * bi2de(reshape(bits, 2, length(bits)/2).') - 3).';

%% Suréchantillonnage
peigne = kron(symboles, [1 zeros(1,Ns-1)]); % peigne de Dirac

%% Filtrage de mise en forme
h = ones(1,Ns);
x = filter(h, 1, peigne); % Filtrage de mise en forme

%% Filtrage de réception
hr = fliplr(h);
n0=length(hr); % prendre la décision à n0*Te+m*Ts pour estimer am emis a mTs
z = filter(hr, 1, x);

%% Diagramme de l'oeil
figure('Name',"Diagramme de l'oeil de la chaine 2 sans bruit");
plot(reshape(z, Ns, length(z)/(Ns)));
title("Diagramme de l'oeil de la chaine 2 sans bruit");

%% Echantillonnage 
zm=z(n0:Ns:end);

%% Démapping + TEB 
bits_recus = reshape(de2bi((zm + 3*Ns)/(2*Ns)).', 1, length(bits));

error=sum(bits_recus~=bits);
TEB2=error/n;

if TEB2 == 0 
    disp('Chaine 2 sans bruit vérifie bien que TEB est nul');
end

%% ----------------------- Avec Bruit --------------------------

EbN0dB=[0:8];
EbN0=10.^(EbN0dB./10);
BER2=zeros(1,length(EbN0));
TES=zeros(1,length(EbN0));
figure('Name', "Chaine2: Diagramme de l'oeil en fonction de EbN0dB");
for k=0:(length(EbN0)-1)
    %% Ajout du bruit
    var_bruit(k+1)=mean(abs(x).^2)*Ns./(2*log2(M).*EbN0(k+1));
    r=x+sqrt(var_bruit(k+1))*randn(1,length(x)); % canal AWGN
    
    %% Filtrage de réception
    z = filter(hr, 1, r);

    %% Diagramme de l'oeil
    subplot(3,3,k+1);
    plot(reshape(z, Ns, length(z)/(Ns)));
    title('EbN0dB = ' , num2str(k));
    %% Echantillonnage 
    zm=z(n0:Ns:end);
    
    %% Démapping + TEB
    % bits_recus = reshape(de2bi((zm + 3)/2).', 1, length(bits));
    tmp = (zm + 3*Ns)/(2*Ns);
    tmp1 = (tmp <0.5)*0 + (0.5<=tmp & tmp<1.5)*1 + (1.5<=tmp & tmp<2.5)*2 + (2.5<=tmp)*3;
    bits_recus = reshape(de2bi(tmp1).', 1, length(bits));
    
    erreur(k+1)=sum(bits_recus~=bits);
    BER2(k+1)=erreur(k+1)/n;
    TES(k+1) = sum(abs(tmp1 - (symboles+3)/2))/length(symboles);
    %disp(['TEB = ', num2str(BER2(k+1)), ' pour EbN0dB = ', num2str(k)]);
end

%% TEB simulé en fct de EBN0dB
figure;
semilogy(EbN0dB,BER2,'p--','LineWidth',3);
xlabel('E_b/N_0 (en dB)');
ylabel('TEB');
title('TEB simulé en fonction de EBN0dB (Chaine 2)');
grid;

%% TES simulé en fct de EBN0dB
figure;
semilogy(EbN0dB,TES,'p--','LineWidth',3);
xlabel('E_b/N_0 (en dB)');
ylabel('TES');
title('TES simulé en fonction de EBN0dB (Chaine 2)');
grid;

%% Comparaison TEB avec TEB théorique
figure;
semilogy(EbN0dB,BER2,'p--','LineWidth',3);
hold on;
semilogy(EbN0dB, qfunc(sqrt(10.^(EbN0dB/10))));
title('Comparaison TEB en fonction du EbN0 en dB avec TEB théorique');
xlabel('EbN0dB');
legend('TEB Simulé', 'TEB Théorique');
hold off;

%% Comparaison TES avec TES théorique
figure;
semilogy(EbN0dB,TES,'p--','LineWidth',3);
hold on;
semilogy(EbN0dB, 3.0/2.0*qfunc(sqrt(4.0/5.0*10.^(EbN0dB/10))));
title('Comparaison TES en fonction du EbN0 en dB avec TES théorique');
xlabel('EbN0dB');
legend('TES Simulé', 'TES Théorique');
hold off;

%% Comparaison TEB avec TEB de la chaine de référence
figure;
semilogy(EbN0dB, BER2);
hold on;
semilogy(EbN0dB, BER);
title('Comparaison TEB en fonction du EbN0 en dB avec chaine de référence');
legend('TEB: Chaine 2','TEB Chaine référence');
xlabel('EbN0dB');
ylabel('TEB');
hold off;

disp('---------------------------');

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% FIN SEQUENCE 3 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% %%