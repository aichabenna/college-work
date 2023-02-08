clear all
close all
%% ------------------------ 8-PSK -------------------------- %

%% Génération de l%information binaire
M = 8;
n = 3000;
bits = randi([0,1], 1, n);

fp = 2000; %Hz fréquence porteuse
fe = 160000; %Hz fréquence d'échantillonnage
Te = 1/fe;
EbN0dB = [0:6];
Rb = 48000;%48000
TEB_th = 10^(-2);
Tb = 1/Rb; %période binaire
Rs = Rb/log2(M); %débit symbole
Ts = 1/Rs; %période symbole
Ns = Ts*fe; %facteur de suréchantillonnage

%% Filtre de cosinus surélevé
alpha = 0.5;
span = 4;
sps = Ns;
h = rcosdesign(alpha, span, sps);

%% Mapping Symboles 8-aires à moyenne nulle 
dataIn = bits';
phaseoffset = 0;
bits_dec = bit2int(dataIn, log2(M));
dk = pskmod(bits_dec,M, phaseoffset,'bin'); %bits <= rangement par log2(M) de bits | essayer avec mode bin

%% Constellation 
ak = real(dk);
bk = imag(dk);
figure('Name', "Constellation  8-PSK (bk = f(ak)) après mapping");
plot(ak,bk,'linestyle','none','marker','o');
title("Constellation  8-PSK (bk = f(ak)) après mapping");

%% Génération de la suite de Diracs pondérés par les symbols (suréchantillonnage)
a2 = kron(dk', [1 zeros(1,Ns-1)]);

%% Filtrage de mise en forme (à revérifier)
xe = filter(h,1,[a2 zeros(1,length(h))]);

%% DSP
[DSP,f] = pwelch(xe,[],[],[],fe,"twosided");
figure;
semilogy(DSP);
title("DSP (8-PSK) sans bruit");

%% x <- xe
x=xe;

%% Filtrage de réception
hr = fliplr(h);
z = filter(hr,1,x); 

%% Echantillonnage 
zm=z(length(hr)+1:Ns:length(z)); 
zm=real(zm)-j*imag(zm);

%% Démapping
tmp1 = pskdemod(zm, M,phaseoffset, 'bin');
tmp2 = de2bi(tmp1,log2(M));
tmp = [tmp2(:,3) tmp2(:,2) tmp2(:,1)];
bits_recus = [];
for i=1:length(tmp2(:,1))
    bits_recus = [bits_recus tmp(i,:)];
end

%% TEB
TEB = sum(bits~=bits_recus);
if sum(bits~=bits_recus)==0
    disp('TEB = 0 (Modulation 8-PSK - sans bruit)');
end

%% ------------------------------------------------------- %%

%% -------------------- Ajout du bruit ------------------- %%
figure('Name', "Constellation  8-PSK (bk = f(ak)) en sortie de l'échantillonage");

Puissance_recu = mean(abs(x).^2);
TEB_bruite_matrice_pbe = zeros(1,7);
TEB_theorique_matrice_pbe = zeros(1,7);
for i = 0:6
    EbN0 = 10^(i/10);
    sigma_n_pbe = sqrt((Puissance_recu*Ns)/(2*log2(M)*(EbN0)));
    bruit_pbe =  sigma_n_pbe * randn(1, length(x)) + j*sigma_n_pbe * randn(1, length(x));
    x_bruite_pbe = x + bruit_pbe;

    %% Filtrage de réception
    z_bruite_pbe = filter(h,1,x_bruite_pbe);
    
    %% Echantillonage
    zm_bruite_pbe=z_bruite_pbe(length(h)+1:Ns:length(z_bruite_pbe));
    
    %% Constellation
    if i<6
        pos = i+1;
    else
        pos =8;
    end
    ak =real(zm_bruite_pbe);
    bk= imag(zm_bruite_pbe);
    subplot(3,3,pos);
    plot(ak,bk,'linestyle','none','marker','o');
    title('EbN0dB = ' , num2str(i));

    tmp1_bruite_pbe = pskdemod(zm_bruite_pbe, M, pi/M);
    tmp2_bruite_pbe = de2bi(tmp1_bruite_pbe);
    tmp_bruite_pbe = [tmp2_bruite_pbe(:,3) tmp2_bruite_pbe(:,2) tmp2_bruite_pbe(:,1)];
    bits_recus_bruite_pbe = [];
    for j=1:length(tmp2_bruite_pbe(:,1))
        bits_recus_bruite_pbe = [bits_recus_bruite_pbe tmp_bruite_pbe(j,:)];
    end

    %% TEB
    erreur_pbe = sum(bits~=bits_recus_bruite_pbe);
    TEB_bruite_pbe = erreur_pbe/n;
    TEB_bruite_matrice_pbe(i+1) = TEB_bruite_pbe;
    if sum(bits~=bits_recus_bruite_pbe)==0
        disp('TEB = 0 (Modulation 8-PSK - avec bruit)');
    end

end
%% ------------------------------------------------------- %%
TEB_theorique_matrice_pbe =  2/log2(M).*qfunc(sqrt(2*log2(M).*EbN0dB) .* sin(pi/M));

%% DSP
[DSP,f] = pwelch(x_bruite_pbe,[],[],[],fe,"twosided");
figure;
semilogy(DSP);
title("DSP (8-PSK) avec bruit");

%% TEB simulé
figure;
semilogy(EbN0dB,TEB_bruite_matrice_pbe,'p--','LineWidth',3);
xlabel('E_b/N_0 (en dB)');
ylabel('TEB');
title('TEB simulé en fonction de EBN0dB ');
grid;


%% Comparaison du TEB simulé au TEB théorique de la chaine étudiée 
figure("Name", 'Comparaison TEB simulée et TEB théorique');
semilogy(EbN0dB,TEB_bruite_matrice_pbe,'p--','LineWidth',3);
hold on;
semilogy(EbN0dB,TEB_theorique_matrice_pbe);
legend('Simulée', 'Théorique');
xlabel('Eb/No (dB)') ;
ylabel('TEB');
title('Comparaison TEB simulée et TEB théorique');

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% FIN %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% %%